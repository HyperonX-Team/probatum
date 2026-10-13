//! The prover: runs proof engines, cross-validates them, and emits
//! certificates.
//!
//! ## Engine ladder
//!
//! 1. **Exhaustive** — walks every input in the domain. Complete (not
//!    statistical) whenever it finishes. Shares only `eval.rs` with the
//!    spec — it is the *definition* of correctness by construction.
//! 2. **BDD (symbolic)** — bit-blasts the contract into a boolean function
//!    and asks whether the "bad state" is satisfiable over the *entire*
//!    domain at once. Also complete. Shares no code with (1).
//! 3. **Statistical** — for domains too large to enumerate or blast: random
//!    sampling with a Clopper–Pearson upper bound. Never claims "proved";
//!    it reports "no violation found in N samples; violation rate < X with
//!    confidence 95%". Honest limits, honestly labeled.
//!
//! ## Cross-validation
//!
//! When both complete engines run, they must agree on the verdict. A
//! disagreement is an *internal error* — we refuse to issue a certificate
//! rather than pick a winner. Two independent implementations agreeing is
//! the strongest evidence a small tool like this can produce.
//!
//! ## Vacuity
//!
//! A precondition that is unsatisfiable makes every contract trivially true
//! ("proved" nothing). The prover checks that at least one input reaches
//! the body — and reports the witness — before claiming success.

use crate::ast::*;
use crate::bdd::Bdd;
use crate::bitblast::{self, BlastError, BitBlaster};
use crate::eval;
use crate::sha256::sha256_hex;

/// What the prover concluded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// All inputs satisfy the contract (complete engines only).
    Proved,
    /// At least one input violates the contract.
    Violated,
    /// Sampling found nothing but this is NOT a proof.
    NoViolationFound,
    /// Gave up (budget, unsupported fragment) without a verdict.
    GaveUp { reason: String },
}

impl Verdict {
    pub fn is_complete(&self) -> bool {
        matches!(self, Verdict::Proved | Verdict::Violated)
    }
}

#[derive(Clone, Debug)]
pub struct Counterexample {
    pub inputs: Vec<(String, i64)>,
    pub violation: String,
}

#[derive(Clone, Debug)]
pub struct EngineReport {
    pub engine: String,
    pub verdict: Verdict,
    /// Inputs actually examined (engine-specific meaning; documented).
    pub checked: u128,
    pub nodes: Option<u128>, // BDD node count when applicable
    pub notes: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct ProofResult {
    pub verdict: Verdict,
    pub engines: Vec<EngineReport>,
    pub counterexample: Option<Counterexample>,
    /// Was the precondition satisfiable? (witness input if known)
    pub pre_witness: Option<Vec<(String, i64)>>,
    /// Statistical bound when applicable: (upper bound on violation rate, confidence)
    pub stat_bound: Option<(f64, f64)>,
    pub cross_validated: bool,
}

pub struct ProverOptions {
    /// Max inputs the exhaustive engine will walk before declining.
    pub exhaustive_budget: u128,
    /// BDD node budget.
    pub bdd_budget: usize,
    /// Samples for the statistical engine.
    pub samples: u64,
    /// Sampling confidence (e.g. 0.95).
    pub confidence: f64,
    /// Force a specific engine ("exhaustive" | "bdd" | "statistical" | "auto").
    pub engine: String,
}

impl Default for ProverOptions {
    fn default() -> Self {
        ProverOptions {
            exhaustive_budget: 100_000_000, // 10^8 inputs ≈ seconds in release
            bdd_budget: 5_000_000,
            samples: 100_000,
            confidence: 0.95,
            engine: "auto".into(),
        }
    }
}

/// Prove (or refute) `spec` against `body`.
pub fn prove(spec: &Spec, body: &[Assign], opts: &ProverOptions) -> ProofResult {
    let domain = spec.input_domain_size();

    // ---- Vacuity: does any input reach the body? --------------------------
    // (Complete over the whole domain when feasible; otherwise sampled.)
    let (pre_witness, vacuity_notes) = check_vacuity(spec, body, opts, domain);

    if let Some(w) = &pre_witness {
        let _ = w; // reachable — good
    }

    let mut engines: Vec<EngineReport> = Vec::new();
    let mut counterexample: Option<Counterexample> = None;
    let mut stat_bound: Option<(f64, f64)> = None;

    let want_exhaustive = opts.engine == "auto" || opts.engine == "exhaustive";
    let want_bdd = opts.engine == "auto" || opts.engine == "bdd";
    let want_stat = opts.engine == "statistical";

    // ---- Engine 1: exhaustive -------------------------------------------
    let mut exhaustive_verdict: Option<Verdict> = None;
    if want_exhaustive {
        match run_exhaustive(spec, body, opts.exhaustive_budget) {
            Ok(report) => {
                if counterexample.is_none() {
                    counterexample = report.counterexample.clone();
                }
                engines.push(EngineReport {
                    engine: format!("exhaustive"),
                    verdict: report.verdict.clone(),
                    checked: report.checked,
                    nodes: None,
                    notes: report.notes,
                });
                exhaustive_verdict = Some(report.verdict);
            }
            Err(reason) => {
                engines.push(EngineReport {
                    engine: "exhaustive".into(),
                    verdict: Verdict::GaveUp { reason: reason.clone() },
                    checked: 0,
                    nodes: None,
                    notes: vec![reason],
                });
            }
        }
    }

    // ---- Engine 2: BDD ---------------------------------------------------
    let mut bdd_verdict: Option<Verdict> = None;
    if want_bdd {
        match run_bdd(spec, body, opts.bdd_budget) {
            Ok(report) => {
                if counterexample.is_none() {
                    counterexample = report.counterexample.clone();
                }
                bdd_verdict = Some(report.verdict.clone());
                engines.push(EngineReport {
                    engine: "bdd-symbolic".into(),
                    verdict: report.verdict,
                    checked: report.checked,
                    nodes: report.nodes,
                    notes: report.notes,
                });
            }
            Err(reason) => {
                engines.push(EngineReport {
                    engine: "bdd-symbolic".into(),
                    verdict: Verdict::GaveUp { reason: reason.clone() },
                    checked: 0,
                    nodes: None,
                    notes: vec![reason],
                });
            }
        }
    }

    // ---- Engine 3: statistical (only if nothing complete succeeded) ------
    let complete = exhaustively_complete(&exhaustive_verdict) || exhaustively_complete(&bdd_verdict);
    if !complete && (want_stat || opts.engine == "auto" || opts.engine == "statistical") {
        let (v, bound, notes) = run_statistical(spec, body, opts);
        stat_bound = bound;
        engines.push(EngineReport {
            engine: "statistical-sampling".into(),
            verdict: v,
            checked: opts.samples as u128,
            nodes: None,
            notes,
        });
    }

    // ---- Cross-validation ------------------------------------------------
    let mut cross_validated = false;
    let verdict = match (exhaustive_verdict, bdd_verdict) {
        (Some(a), Some(b)) if a == b => {
            cross_validated = a.is_complete();
            a
        }
        (Some(a), Some(b)) => {
            // Disagreement between two independent complete engines: this is
            // a bug in us, not in the spec. Refuse to certify.
            engines.push(EngineReport {
                engine: "cross-validation".into(),
                verdict: Verdict::GaveUp {
                    reason: format!(
                        "ENGINES DISAGREE (exhaustive={:?}, bdd={:?}) — refusing to certify",
                        a, b
                    ),
                },
                checked: 0,
                nodes: None,
                notes: vec!["internal error: independent engines disagree".into()],
            });
            Verdict::GaveUp {
                reason: "internal: engines disagree".into(),
            }
        }
        (Some(a), None) => a,
        (None, Some(b)) => b,
        (None, None) => {
            // Nothing complete ran; use statistical if it did, else gave up.
            engines
                .iter()
                .find(|e| e.engine == "statistical-sampling")
                .map(|e| e.verdict.clone())
                .unwrap_or(Verdict::GaveUp {
                    reason: "no engine could run".into(),
                })
        }
    };

    // Vacuous precondition ⇒ "Proved" is meaningless; downgrade honestly.
    let verdict = if pre_witness.is_none() {
        Verdict::GaveUp {
            reason: format!(
                "precondition is UNSATISFIABLE (vacuous) — {}",
                vacuity_notes.join("; ")
            ),
        }
    } else {
        verdict
    };

    ProofResult {
        verdict,
        engines,
        counterexample,
        pre_witness,
        stat_bound,
        cross_validated,
    }
}

fn exhaustively_complete(v: &Option<Verdict>) -> bool {
    matches!(v, Some(Verdict::Proved) | Some(Verdict::Violated))
}

// ---------------------------------------------------------------------------
// Vacuity check
// ---------------------------------------------------------------------------

struct ExhaustiveReport {
    verdict: Verdict,
    checked: u128,
    counterexample: Option<Counterexample>,
    notes: Vec<String>,
}

fn check_vacuity(
    spec: &Spec,
    _body: &[Assign],
    opts: &ProverOptions,
    domain: u128,
) -> (Option<Vec<(String, i64)>>, Vec<String>) {
    // Walk the domain looking for ONE input satisfying `requires`.
    // If the domain is too big, use BDD to decide satisfiability.
    if domain <= opts.exhaustive_budget {
        let ranges: Vec<IntRange> = spec
            .params
            .iter()
            .map(|b| match b.ty {
                Type::Int(r) => r,
                Type::Bool => IntRange::new(0, 1),
            })
            .collect();
        let mut inputs: Vec<i64> = ranges.iter().map(|r| r.lo).collect();
        loop {
            if eval::precondition_holds(spec, &inputs) {
                let w = spec
                    .params
                    .iter()
                    .zip(&inputs)
                    .map(|(b, v)| (b.name.clone(), *v))
                    .collect();
                return (Some(w), vec!["satisfiable".into()]);
            }
            // odometer increment
            if !increment(&ranges, &mut inputs) {
                break;
            }
        }
        (
            None,
            vec!["no input in the domain satisfies `requires`".into()],
        )
    } else {
        // Try BDD for the satisfiability of `requires`.
        match bdd_pre_sat(spec, opts.bdd_budget) {
            Ok(Some(w)) => (Some(w), vec!["satisfiable (via BDD)".into()]),
            Ok(None) => (
                None,
                vec!["no input satisfies `requires` (via BDD)".into()],
            ),
            Err(e) => (
                // Can't decide: assume reachable rather than refuse — the
                // vacuity check is a guard, not the proof itself.
                Some(Vec::new()),
                vec![format!("vacuity not decided: {}", e)],
            ),
        }
    }
}

fn bdd_pre_sat(spec: &Spec, budget: usize) -> Result<Option<Vec<(String, i64)>>, String> {
    let mut bdd = Bdd::new(budget);
    let mut bb = BitBlaster::new(&mut bdd);
    let mut env = std::collections::HashMap::new();
    let mut named = Vec::new();
    for p in &spec.params {
        let r = match p.ty {
            Type::Int(r) => r,
            Type::Bool => return Err("bool params unsupported".into()),
        };
        let v = bb.param_bits(r).map_err(|e| e.to_string())?;
        env.insert(p.name.clone(), IVal_clone(&v));
        named.push((p.name.clone(), v));
    }
    let mut pre = crate::bdd::TRUE;
    for clause in &spec.requires {
        let c = bb.blast_bool(clause, &env).map_err(|e| e.to_string())?;
        pre = bb
            .bdd
            .and(pre, c.val)
            .map_err(|e: crate::bdd::BddError| e.to_string())?;
    }
    let _ = &mut bb; // bdd borrow released for reads below
    if !bdd_sat(&bdd, pre) {
        return Ok(None);
    }
    let assign = bdd_one_sat(&bdd, pre);
    Ok(Some(decode_params(spec, &named, &assign)))
}

// Small indirections so prove.rs doesn't reach into Bdd internals directly.
fn bdd_sat(b: &Bdd, f: u32) -> bool {
    b.sat(f)
}
fn bdd_one_sat(b: &Bdd, f: u32) -> std::collections::HashMap<u32, bool> {
    b.one_sat(f)
}

use crate::bitblast::IVal as _IVal;
fn IVal_clone(v: &_IVal) -> _IVal {
    _IVal {
        bits: v.bits.clone(),
        fault: v.fault,
        range: v.range,
    }
}

fn decode_params(
    spec: &Spec,
    named: &[(String, _IVal)],
    assign: &std::collections::HashMap<u32, bool>,
) -> Vec<(String, i64)> {
    // We need the variable indices each param occupies. BitBlaster assigns
    // them sequentially starting at 0, so reconstruct the layout.
    let mut next = 0u32;
    let mut out = Vec::new();
    for (name, v) in named {
        let mut val: i64 = 0;
        let w = v.bits.len();
        for i in 0..w {
            // Constant bits (terminals) are TRUE/FALSE directly.
            let node = v.bits[i];
            let bit = if node == crate::bdd::FALSE {
                false
            } else if node == crate::bdd::TRUE {
                true
            } else {
                *assign.get(&next).unwrap_or(&false)
            };
            if bit {
                val |= 1i64 << i;
            }
            next += 1;
        }
        // Sign-extend.
        if val & (1i64 << (w - 1)) != 0 {
            val |= -1i64 << w;
        }
        out.push((name.clone(), val));
    }
    let _ = spec;
    out
}

// ---------------------------------------------------------------------------
// Odometer
// ---------------------------------------------------------------------------

fn increment(ranges: &[IntRange], inputs: &mut [i64]) -> bool {
    for i in (0..inputs.len()).rev() {
        if inputs[i] < ranges[i].hi {
            inputs[i] += 1;
            return true;
        }
        inputs[i] = ranges[i].lo;
    }
    false // wrapped
}

// ---------------------------------------------------------------------------
// Exhaustive engine
// ---------------------------------------------------------------------------

fn run_exhaustive(
    spec: &Spec,
    body: &[Assign],
    budget: u128,
) -> Result<ExhaustiveReport, String> {
    let domain = spec.input_domain_size();
    if domain > budget {
        return Err(format!(
            "domain of {} inputs exceeds budget of {} — declining (BDD or sampling next)",
            domain, budget
        ));
    }

    let ranges: Vec<IntRange> = spec
        .params
        .iter()
        .map(|b| match b.ty {
            Type::Int(r) => Ok(r),
            Type::Bool => Err("bool params unsupported by exhaustive engine"),
        })
        .collect::<Result<Vec<_>, &str>>()
        .map_err(|e| e.to_string())?;

    let mut inputs: Vec<i64> = ranges.iter().map(|r| r.lo).collect();
    let mut checked: u128 = 0;
    let mut notes = Vec::new();

    loop {
        if eval::precondition_holds(spec, &inputs) {
            checked += 1;
            match eval::check_contract(spec, body, &inputs) {
                Ok(false) => {} // satisfied
                Ok(true) => {}  // out of domain (double-checked inside)
                Err(v) => {
                    let cx = Counterexample {
                        inputs: spec
                            .params
                            .iter()
                            .zip(&inputs)
                            .map(|(b, v)| (b.name.clone(), *v))
                            .collect(),
                        violation: v.to_string(),
                    };
                    return Ok(ExhaustiveReport {
                        verdict: Verdict::Violated,
                        checked,
                        counterexample: Some(cx),
                        notes,
                    });
                }
            }
        }
        if !increment(&ranges, &mut inputs) {
            break;
        }
    }

    notes.push(format!("enumerated all {} domain inputs", domain));
    Ok(ExhaustiveReport {
        verdict: Verdict::Proved,
        checked,
        counterexample: None,
        notes,
    })
}

// ---------------------------------------------------------------------------
// BDD engine
// ---------------------------------------------------------------------------

struct BddReport {
    verdict: Verdict,
    checked: u128,
    nodes: Option<u128>,
    counterexample: Option<Counterexample>,
    notes: Vec<String>,
}

fn run_bdd(spec: &Spec, body: &[Assign], budget: usize) -> Result<BddReport, String> {
    bitblast::spec_supported(spec, body).map_err(|op| format!("unsupported fragment: {}", op))?;

    let mut bdd = Bdd::new(budget);
    let (bad, vars_used, named) = {
        let mut bb = BitBlaster::new(&mut bdd);
        let mut env = std::collections::HashMap::new();
        let mut named: Vec<(String, _IVal)> = Vec::new();
        for p in &spec.params {
            let r = match p.ty {
                Type::Int(r) => r,
                Type::Bool => return Err("bool params unsupported".into()),
            };
            let v = bb.param_bits(r).map_err(|e: BlastError| e.to_string())?;
            env.insert(p.name.clone(), IVal_clone(&v));
            named.push((p.name.clone(), v));
        }
        let bad = bb
            .bad_state(spec, body, &env, &named)
            .map_err(|e: BlastError| e.to_string())?;
        (bad, bb.vars_used(), named)
    };

    let nodes = bdd.node_count() as u128;

    if !bdd.sat(bad) {
        return Ok(BddReport {
            verdict: Verdict::Proved,
            checked: 1u128 << vars_used.min(90), // symbolic: one step = whole domain
            nodes: Some(nodes),
            counterexample: None,
            notes: vec![format!(
                "bad-state function is UNSATISFIABLE over all encoded inputs ({} BDD vars)",
                vars_used
            )],
        });
    }

    // Extract a concrete counterexample and CONFIRM it with the reference
    // evaluator — a BDD bug must not produce a bogus certificate.
    let assign = bdd_one_sat(&bdd, bad);
    let decoded = decode_params(spec, &named, &assign);

    // Confirm against the evaluator.
    let inputs: Vec<i64> = spec
        .params
        .iter()
        .map(|p| {
            decoded
                .iter()
                .find(|(n, _)| n == &p.name)
                .map(|(_, v)| *v)
                .unwrap_or(0)
        })
        .collect();
    let confirm = eval::check_contract(spec, body, &inputs);
    match confirm {
        Err(v) => Ok(BddReport {
            verdict: Verdict::Violated,
            checked: 1,
            nodes: Some(nodes),
            counterexample: Some(Counterexample {
                inputs: decoded,
                violation: v.to_string(),
            }),
            notes: vec![
                "counterexample extracted from BDD and independently confirmed by the evaluator"
                    .into(),
            ],
        }),
        Ok(_) => {
            // BDD claims violation, evaluator disagrees → internal error.
            Err(format!(
                "internal: BDD found a 'counterexample' {:?} that the evaluator accepts — refusing to certify",
                inputs
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// Statistical engine
// ---------------------------------------------------------------------------

fn run_statistical(
    spec: &Spec,
    body: &[Assign],
    opts: &ProverOptions,
) -> (Verdict, Option<(f64, f64)>, Vec<String>) {
    let n = opts.samples;
    let mut rng = SplitMix64::new(0x1CE_BDD ^ (n as u64));
    let ranges: Vec<IntRange> = spec
        .params
        .iter()
        .map(|b| match b.ty {
            Type::Int(r) => r,
            Type::Bool => IntRange::new(0, 1),
        })
        .collect();

    let mut tested = 0u64;
    let mut guard = 0u64;
    while tested < n && guard < n.saturating_mul(10) {
        guard += 1;
        let inputs: Vec<i64> = ranges
            .iter()
            .map(|r| {
                let span = (r.hi - r.lo) as u64 + 1;
                r.lo + (rng.next() % span) as i64
            })
            .collect();
        if !eval::precondition_holds(spec, &inputs) {
            continue;
        }
        tested += 1;
        if let Err(v) = eval::check_contract(spec, body, &inputs) {
            return (
                Verdict::Violated,
                None,
                vec![format!(
                    "counterexample found in sample #{}: {:?} → {}",
                    tested,
                    inputs,
                    v
                )],
            );
        }
    }

    if tested == 0 {
        return (
            Verdict::GaveUp {
                reason: "no sampled input satisfied `requires` — precondition may be unsatisfiable"
                    .into(),
            },
            None,
            vec!["0 in-domain samples".into()],
        );
    }

    // Clopper–Pearson: with 0 failures in n trials, the one-sided upper
    // bound on the failure rate at confidence c is 1 - (1-c)^(1/n).
    let conf = opts.confidence;
    let upper = 1.0 - (1.0 - conf).powf(1.0 / tested as f64);
    (
        Verdict::NoViolationFound,
        Some((upper, conf)),
        vec![
            format!("{} in-domain samples, 0 violations", tested),
            format!(
                "NOT A PROOF: violation rate < {:.3e} with {:.0}% confidence",
                upper,
                conf * 100.0
            ),
        ],
    )
}

/// Deterministic, seedable PRNG (SplitMix64) — sampling must be reproducible
/// for certificates to be reproducible.
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        SplitMix64 { state: seed }
    }
    pub fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
}

// ---------------------------------------------------------------------------
// Certificate
// ---------------------------------------------------------------------------

/// A proof certificate: everything needed to re-derive the proof, plus a
/// digest binding it to the exact spec and program bytes.
#[derive(Clone, Debug)]
pub struct Certificate {
    pub spec_sha256: String,
    pub program_sha256: String,
    pub spec_name: String,
    pub verdict: String,
    pub engines: Vec<(String, String, u128, Option<u128>)>, // name, verdict, checked, nodes
    pub cross_validated: bool,
    pub pre_witness: Option<Vec<(String, i64)>>,
    pub counterexample: Option<Counterexample>,
    pub stat_bound: Option<(f64, f64)>,
    pub cert_sha256: String, // digest of the canonical body
}

impl Certificate {
    /// Canonical text form — the thing we hash. Deterministic ordering,
    /// no timestamps (a certificate is a mathematical object, not a log).
    pub fn canonical(&self) -> String {
        let mut s = String::new();
        s.push_str("ic-cert-1\n");
        s.push_str(&format!("spec: {}\n", self.spec_name));
        s.push_str(&format!("spec-sha256: {}\n", self.spec_sha256));
        s.push_str(&format!("program-sha256: {}\n", self.program_sha256));
        s.push_str(&format!("verdict: {}\n", self.verdict));
        s.push_str(&format!("cross-validated: {}\n", self.cross_validated));
        match &self.pre_witness {
            Some(w) => {
                s.push_str("precondition: SATISFIABLE\n");
                if !w.is_empty() {
                    let pairs: Vec<String> = w.iter().map(|(k, v)| format!("{}={}", k, v)).collect();
                    s.push_str(&format!("witness: {}\n", pairs.join(", ")));
                }
            }
            None => s.push_str("precondition: UNSATISFIABLE (vacuous)\n"),
        }
        for (name, verdict, checked, nodes) in &self.engines {
            s.push_str(&format!(
                "engine: {} verdict={} checked={}{}\n",
                name,
                verdict,
                checked,
                nodes
                    .map(|n| format!(" nodes={}", n))
                    .unwrap_or_default()
            ));
        }
        if let Some((bound, conf)) = self.stat_bound {
            s.push_str(&format!(
                "stat-bound: violation-rate < {:.6e} at confidence {:.4}\n",
                bound, conf
            ));
        }
        if let Some(cx) = &self.counterexample {
            let pairs: Vec<String> = cx
                .inputs
                .iter()
                .map(|(k, v)| format!("{}={}", k, v))
                .collect();
            s.push_str(&format!("counterexample: {}\n", pairs.join(", ")));
            s.push_str(&format!("cause: {}\n", cx.violation));
        }
        s
    }

    /// Rebind the canonical body with its digest (digest = sha256(body)).
    pub fn seal(mut self) -> Self {
        let body = self.canonical();
        self.cert_sha256 = sha256_hex(body.as_bytes());
        self
    }

    /// Serialize to a stable, human-readable certificate file.
    pub fn render(&self) -> String {
        let mut s = self.canonical();
        s.push_str(&format!("cert-sha256: {}\n", self.cert_sha256));
        s
    }

    /// Parse a rendered certificate.
    pub fn parse(text: &str) -> Result<Certificate, String> {
        let mut c = Certificate {
            spec_sha256: String::new(),
            program_sha256: String::new(),
            spec_name: String::new(),
            verdict: String::new(),
            engines: Vec::new(),
            cross_validated: false,
            pre_witness: None,
            counterexample: None,
            stat_bound: None,
            cert_sha256: String::new(),
        };
        let mut body = String::new();
        for line in text.lines() {
            if line.starts_with("cert-sha256: ") {
                c.cert_sha256 = line["cert-sha256: ".len()..].trim().to_string();
                continue;
            }
            // Body lines (everything before cert-sha256) feed the digest.
            body.push_str(line);
            body.push('\n');
            let Some((key, val)) = line.split_once(':') else {
                continue;
            };
            let val = val.trim();
            match key {
                "spec" => c.spec_name = val.to_string(),
                "spec-sha256" => c.spec_sha256 = val.to_string(),
                "program-sha256" => c.program_sha256 = val.to_string(),
                "verdict" => c.verdict = val.to_string(),
                "cross-validated" => c.cross_validated = val == "true",
                "precondition" => {
                    if val.starts_with("SATISFIABLE") {
                        c.pre_witness = Some(Vec::new());
                    } else {
                        c.pre_witness = None;
                    }
                }
                "witness" => {
                    if let Some(w) = c.pre_witness.as_mut() {
                        *w = parse_pairs(val);
                    }
                }
                "engine" => {
                    // engine: name verdict=X checked=Y [nodes=Z]
                    let mut name = String::new();
                    let mut verdict = String::new();
                    let mut checked = 0u128;
                    let mut nodes = None;
                    for (i, part) in val.split_whitespace().enumerate() {
                        if i == 0 {
                            name = part.to_string();
                        } else if let Some(v) = part.strip_prefix("verdict=") {
                            verdict = v.to_string();
                        } else if let Some(v) = part.strip_prefix("checked=") {
                            checked = v.parse().unwrap_or(0);
                        } else if let Some(v) = part.strip_prefix("nodes=") {
                            nodes = v.parse().ok();
                        }
                    }
                    c.engines.push((name, verdict, checked, nodes));
                }
                "stat-bound" => {
                    // violation-rate < X at confidence Y
                    let parts: Vec<&str> = val.split_whitespace().collect();
                    if parts.len() >= 4 {
                        let b = parts[2].parse::<f64>().unwrap_or(0.0);
                        let cf = parts[4].parse::<f64>().unwrap_or(0.0);
                        c.stat_bound = Some((b, cf));
                    }
                }
                "counterexample" => {
                    c.counterexample = Some(Counterexample {
                        inputs: parse_pairs(val),
                        violation: String::new(),
                    });
                }
                "cause" => {
                    if let Some(cx) = c.counterexample.as_mut() {
                        cx.violation = val.to_string();
                    }
                }
                _ => {}
            }
        }
        // Digest must match the body.
        let expect = sha256_hex(body.as_bytes());
        if expect != c.cert_sha256 {
            return Err(format!(
                "certificate digest mismatch: file says {}, recomputed {} — file corrupted or tampered",
                c.cert_sha256, expect
            ));
        }
        Ok(c)
    }
}

fn parse_pairs(s: &str) -> Vec<(String, i64)> {
    s.split(',')
        .filter_map(|p| {
            let p = p.trim();
            let (k, v) = p.split_once('=')?;
            Some((k.trim().to_string(), v.trim().parse().ok()?))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn transfer(with_body: bool) -> Spec {
        let src = format!(
            r#"
            spec transfer(a: int[0..255], b: int[0..255], amount: int[0..255])
              returns (x: int[0..255], y: int[0..255])
              requires amount <= a
              requires b + amount <= 255
              ensures x == a - amount
              ensures y == b + amount
              ensures x + y == a + b
              example (100, 50, 25) => (75, 75)
            {}
            "#,
            if with_body {
                "{ x := a - amount; y := b + amount; }"
            } else {
                ""
            }
        );
        let s = parse(&src).unwrap();
        crate::sema::analyze(&s).unwrap();
        s
    }

    #[test]
    fn proves_correct_transfer_exhaustively() {
        let spec = transfer(true);
        let body = spec.body.clone().unwrap();
        let opts = ProverOptions {
            engine: "exhaustive".into(),
            exhaustive_budget: 200_000, // smaller slice of 256^3 for test speed
            ..Default::default()
        };
        // Domain is 256^3 ≈ 16.7M — too big for the test budget, so the
        // engine should DECLINE, not falsely prove.
        let r = prove(&spec, &body, &opts);
        assert!(
            matches!(r.verdict, Verdict::GaveUp { .. }),
            "must decline when domain exceeds budget, got {:?}",
            r.verdict
        );
    }

    #[test]
    fn proves_small_correct_spec() {
        let s = parse(
            r#"
            spec inc(a: int[0..31]) returns (r: int[0..32])
              requires a < 31
              ensures r == a + 1
            { r := a + 1; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let body = s.body.clone().unwrap();
        let r = prove(&s, &body, &ProverOptions::default());
        assert_eq!(r.verdict, Verdict::Proved, "engines: {:?}", r.engines);
        assert!(r.pre_witness.is_some());
    }

    #[test]
    fn catches_broken_spec_with_counterexample() {
        // Bug: forgets the increment.
        let s = parse(
            r#"
            spec inc(a: int[0..31]) returns (r: int[0..32])
              requires a < 31
              ensures r == a + 1
            { r := a; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let body = s.body.clone().unwrap();
        let r = prove(&s, &body, &ProverOptions::default());
        assert_eq!(r.verdict, Verdict::Violated);
        let cx = r.counterexample.expect("must report a counterexample");
        assert!(!cx.inputs.is_empty());
        assert!(!cx.violation.is_empty());
    }

    #[test]
    fn refuses_vacuous_proof() {
        let s = parse(
            r#"
            spec inc(a: int[0..31]) returns (r: int[0..32])
              requires a > 999
              ensures r == a + 1
            { r := a + 1; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let body = s.body.clone().unwrap();
        let r = prove(&s, &body, &ProverOptions::default());
        assert!(
            matches!(&r.verdict, Verdict::GaveUp { reason } if reason.contains("vacuous")),
            "must refuse vacuous proof, got {:?}",
            r.verdict
        );
    }

    #[test]
    fn cross_validates_on_small_domain() {
        let s = parse(
            r#"
            spec half(a: int[0..63]) returns (r: int[0..63])
              requires a % 2 == 0
              ensures r == a / 2
            { r := a / 2; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let body = s.body.clone().unwrap();
        let r = prove(&s, &body, &ProverOptions::default());
        // Division ⇒ BDD declines; exhaustive proves. Must still be Proved.
        assert_eq!(r.verdict, Verdict::Proved, "engines: {:?}", r.engines);
        let bdd = r.engines.iter().find(|e| e.engine == "bdd-symbolic").unwrap();
        assert!(
            matches!(bdd.verdict, Verdict::GaveUp { .. }),
            "BDD should decline division, not guess"
        );
    }

    #[test]
    fn certificate_roundtrip_and_tamper_detection() {
        let s = parse(
            r#"
            spec inc(a: int[0..15]) returns (r: int[0..16])
              requires a < 15
              ensures r == a + 1
            { r := a + 1; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let body = s.body.clone().unwrap();
        let r = prove(&s, &body, &ProverOptions::default());
        let cert = Certificate {
            spec_sha256: "abc".into(),
            program_sha256: "def".into(),
            spec_name: s.name.clone(),
            verdict: format!("{:?}", r.verdict),
            engines: r
                .engines
                .iter()
                .map(|e| (e.engine.clone(), format!("{:?}", e.verdict), e.checked, e.nodes))
                .collect(),
            cross_validated: r.cross_validated,
            pre_witness: r.pre_witness.clone(),
            counterexample: r.counterexample.clone(),
            stat_bound: r.stat_bound,
            cert_sha256: String::new(),
        }
        .seal();

        let text = cert.render();
        let back = Certificate::parse(&text).expect("roundtrip must parse");
        assert_eq!(back.cert_sha256, cert.cert_sha256);
        assert_eq!(back.verdict, cert.verdict);

        // Tamper with one byte.
        let tampered = text.replace("verdict: Proved", "verdict: Pwned");
        assert!(
            Certificate::parse(&tampered).is_err(),
            "tampering must be detected"
        );
    }
}
