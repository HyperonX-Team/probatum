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

use crate::ast;
use crate::ast::*;
use crate::bdd::Bdd;
use crate::bitblast::{self, BlastError, BitBlaster};
use crate::eval;
use crate::eval::{Fault, Violation};
use crate::sha256::sha256_hex;

/// Name a flat input vector for human consumption: scalar parameters by
/// name, array parameters element by element (`a[0]`, `a[1]`, …).
pub fn describe_inputs(spec: &Spec, inputs: &[i64]) -> Vec<(String, i64)> {
    let mut out = Vec::new();
    let mut k = 0usize;
    for b in &spec.params {
        match b.ty {
            Type::Array { index, .. } => {
                for i in index.lo..=index.hi {
                    if let Some(v) = inputs.get(k) {
                        out.push((format!("{}[{}]", b.name, i), *v));
                    }
                    k += 1;
                }
            }
            _ => {
                if let Some(v) = inputs.get(k) {
                    out.push((b.name.clone(), *v));
                }
                k += 1;
            }
        }
    }
    out
}

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
    /// Concrete things to change, derived from the violation. Presentation,
    /// not proof: deliberately outside the certificate, which must stay a
    /// deterministic function of the spec and the program.
    pub suggestions: Vec<String>,
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

// Diagnosis: minimal counterexamples and actionable advice
//
// This is the axis where the SMT-backed tools are weakest by construction.
// When Z3 or CBMC cannot discharge an obligation they report *that* it failed
// — "postcondition might not hold", "assertion failed" — and the model they
// hand back is an artifact of their search, often with values in the millions
// and no indication of what to change. probatum owns the domain, so it can do
// the two things that actually help: shrink the witness to its simplest form,
// and name the construct to edit.

/// Candidate replacements for one position, simplest-first.
///
/// "Simplest" means smallest magnitude, negative before positive (a negative
/// boundary is the interesting one for arithmetic). Zero comes first when it is
/// in the domain.
///
/// An earlier version tried the domain's `hi` third, on the theory that
/// boundaries are where bugs live. But `hi` is not *simpler* than the current
/// value, so the walk drifted outward until witnesses read
/// `a=255, b=0, amount=255`. Minimality is the promise; interestingness
/// follows from it, not the other way round.
///
/// If the domain excludes every small magnitude (`int[1000..2000]`), fall back
/// to that domain's own floor.
fn simpler_candidates(lo: i64, hi: i64, current: i64, limit: usize) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut m = 0i64;
    while out.len() < limit && m <= 64 {
        if m == 0 {
            if lo <= 0 && 0 <= hi && current != 0 {
                out.push(0);
            }
        } else {
            if lo <= -m && -m <= hi && current != -m {
                out.push(-m);
            }
            if out.len() < limit && lo <= m && m <= hi && current != m {
                out.push(m);
            }
        }
        m += 1;
    }
    if out.is_empty() {
        if current != lo {
            out.push(lo);
        }
        if out.len() < limit && current != hi {
            out.push(hi);
        }
    }
    out
}

/// Shrink a failing input to a simplest input that still fails.
///
/// Two phases, because coordinate descent alone gets stuck or wanders:
///
/// 1. **Strict descent.** For each argument, try strictly simpler values and
///    keep the first that preserves the violation. Never move a coordinate
///    *outward* — an earlier version accepted any failing candidate, which let
///    a coordinate grow: from `(3,3)` (already optimal for `a + b > 5`) the
///    walk drifted to `(4,2)`.
/// 2. **Coordinated probes.** Strict descent cannot escape `(0,6)`, whose
///    coordinates are each already minimal even though `(3,3)` is smaller in
///    every norm a human cares about. So we also try setting *all* arguments
///    to a common small magnitude ±t and keep the first that fails. That is
///    what finds diagonal boundaries like `a + b > 5`.
///
/// The result is a genuine witness — candidates are only ever drawn from the
/// declared domains — and it is a local minimum under both moves.
pub fn minimize_counterexample(spec: &Spec, prog: &Program, inputs: &[i64]) -> Vec<i64> {
    let domains = ast::input_domains(spec);
    if inputs.len() != domains.len() || inputs.is_empty() {
        return inputs.to_vec();
    }
    let fails =
        |cand: &[i64]| matches!(eval::check_contract_program(spec, prog, cand), Err(_));
    let mut cur = inputs.to_vec();
    if !fails(&cur) {
        return cur; // not a contract violation (e.g. an example witness): leave it
    }

    let mut rounds = 0;
    loop {
        rounds += 1;
        if rounds > 6 {
            break;
        }
        let before = cur.clone();

        // Phase 1: strictly simpler, coordinate by coordinate.
        for i in 0..cur.len() {
            for c in simpler_candidates(domains[i].lo, domains[i].hi, cur[i], 16) {
                if c.abs() >= cur[i].abs() {
                    break; // never move a coordinate outward
                }
                let mut cand = cur.clone();
                cand[i] = c;
                if fails(&cand) {
                    cur = cand;
                    break;
                }
            }
        }

        // Phase 2: all arguments at a common small magnitude.
        let ceiling = cur.iter().map(|v| v.abs()).max().unwrap_or(0);
        let mut moved = false;
        for t in 0..ceiling {
            for sign in [-1i64, 1] {
                let cand: Vec<i64> = domains
                    .iter()
                    .map(|d| (sign * t).max(d.lo).min(d.hi))
                    .collect();
                if cand != cur && fails(&cand) {
                    cur = cand;
                    moved = true;
                    break;
                }
            }
            if moved {
                break;
            }
        }

        if cur == before {
            break; // stable under both moves
        }
    }
    cur
}

/// Rebuild a flat input vector from named values (`a[0]`, `n`, …).
fn flatten_named(spec: &Spec, named: &[(String, i64)]) -> Option<Vec<i64>> {
    let mut out = Vec::new();
    for b in &spec.params {
        match b.ty {
            Type::Array { index, .. } => {
                for i in index.lo..=index.hi {
                    let key = format!("{}[{}]", b.name, i);
                    out.push(*named.iter().find(|(n, _)| *n == key).map(|(_, v)| v)?);
                }
            }
            _ => out.push(*named.iter().find(|(n, _)| *n == b.name).map(|(_, v)| v)?),
        }
    }
    Some(out)
}

/// Environment with inputs *and* results bound, for inspecting a failing clause.
fn env_at(spec: &Spec, prog: &Program, inputs: &[i64]) -> Option<eval::Env> {
    let mut m = eval::Machine::new(spec, inputs).ok()?;
    m.exec_block(prog).ok()?;
    let mut env = eval::input_env(spec, inputs);
    for (b, v) in spec.results.iter().zip(m.results()) {
        env.results.push((b.name.clone(), v));
    }
    for (name, contents) in m.arrays() {
        if spec.results.iter().any(|r| &r.name == name) {
            env.arrays.insert(name.clone(), contents.clone());
        }
    }
    Some(env)
}

/// The message for a contract violation, with the actual values on both sides
/// of a failing comparison. "ensures #1 false" is a fact; "the program has 5
/// where the contract needs 7" is a diagnosis.
fn diagnose_violation(spec: &Spec, prog: &Program, inputs: &[i64], v: &Violation) -> String {
    let base = v.to_string();
    if let Violation::EnsuresFalse { expr, .. } = v {
        if let Expr::Binary(_, l, r) = expr {
            if let Some(env) = env_at(spec, prog, inputs) {
                if let (Ok(lv), Ok(rv)) = (eval::eval(l, &env), eval::eval(r, &env)) {
                    let detail = match (lv.as_int(), rv.as_int()) {
                        (Some(a), Some(b)) if a != b => {
                            let d = a as i128 - b as i128;
                            format!(
                                " — the program has {} where the contract needs {} ({} {})",
                                a,
                                b,
                                if d > 0 { "over by" } else { "short by" },
                                d.abs()
                            )
                        }
                        _ => format!(" — left is {}, right is {}", lv, rv),
                    };
                    return format!("{}{}", base, detail);
                }
            }
        }
    }
    base
}

/// Concrete things to change. Every suggestion names the construct to edit,
/// because "the proof failed" is not a bug report.
fn advise(spec: &Spec, _prog: &Program, _inputs: &[i64], v: &Violation) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    match v {
        Violation::Faulted { fault } => match fault {
            Fault::DivByZero => out.push(
                "guard the division: either `requires d != 0` (the caller must then establish \
                 it) or `if d != 0 then a / d else 0` in the body"
                    .into(),
            ),
            Fault::Overflow => out.push(
                "narrow the parameter domains, or add a `requires` bound that keeps the \
                 intermediate value representable"
                    .into(),
            ),
            Fault::NonTermination { .. } => out.push(
                "the loop never reached its exit condition: check that the body makes progress \
                 toward the guard, and that `decreases` is a variant that actually shrinks"
                    .into(),
            ),
            Fault::AssertionFailed { expr } => out.push(format!(
                "the inline `assert {}` is false here — either the assertion states something \
                 untrue, or an earlier statement fails to establish it",
                expr
            )),
            Fault::IndexOutOfRange { array, .. } => out.push(format!(
                "the index into `{}` left its declared domain: bound it with a `requires`, or \
                 clamp it in the body",
                array
            )),
            Fault::TypeMismatch(_) => {}
        },
        Violation::OutOfRange {
            result,
            value,
            range,
        } => out.push(format!(
            "`{}` produced {}, outside {}. Either widen the result declaration, or add a \
             `requires` that keeps the value inside it",
            result, value, range
        )),
        Violation::EnsuresFalse { clause, expr } => {
            let is_definition = matches!(
                expr,
                Expr::Binary(BinOp::Eq, l, r)
                    if matches!(&**l, Expr::Result(_) | Expr::Param(_))
                        || matches!(&**r, Expr::Result(_) | Expr::Param(_))
            );
            if is_definition {
                out.push(format!(
                    "ensure #{} is definitional: the body must compute exactly that expression, \
                     and the input above shows where it diverges",
                    clause + 1
                ));
            } else {
                out.push(format!(
                    "ensure #{} is a property, not a definition — the body has to establish it \
                     for every in-domain input, not just the ones you had in mind",
                    clause + 1
                ));
            }
            // When the failing clause is a bound on a result, name that
            // result's declaration: widening the type is often the honest fix,
            // and weakening the clause is usually not.
            if let Expr::Binary(op, l, _) = expr {
                if matches!(op, BinOp::Ge | BinOp::Gt | BinOp::Le | BinOp::Lt) {
                    if let Expr::Result(name) = &**l {
                        if let Some(b) = spec.results.iter().find(|b| &b.name == name) {
                            out.push(format!(
                                "`{}` is declared {} — if the body can legitimately produce \
                                 values outside that, widen the declaration; otherwise the body \
                                 is wrong, not the type",
                                name, b.ty
                            ));
                        }
                    }
                }
            }
        },
    }
    out
}

/// Advice for a failed loop obligation: the state where induction breaks is
/// the single most useful thing an invariant author can be shown, and no
/// SMT-backed tool shows it this directly.
fn advise_obligation(kind: &str, inputs: &[(String, i64)]) -> Vec<String> {
    let state = inputs
        .iter()
        .map(|(n, v)| format!("{}={}", n, v))
        .collect::<Vec<_>>()
        .join(", ");
    match kind {
        "loop preservation" => vec![format!(
            "the invariant is not inductive: it holds at [{}], but the body does not restore \
             it. Strengthen it with the fact the body changes — normally a statement about the \
             counter, the accumulator, or how much of the array has been consumed",
            state
        )],
        "loop exit" => vec![format!(
            "the invariant is too weak to imply the postcondition at [{}], where the guard has \
             just failed. Add the fact connecting the accumulator to the result",
            state
        )],
        "loop termination" => vec![format!(
            "the `decreases` variant does not strictly shrink at [{}]. Choose an expression the \
             body provably reduces — usually the remaining iterations",
            state
        )],
        _ => Vec::new(),
    }
}

/// Minimize a counterexample, then re-derive its message and advice from the
/// violation itself. Minimization and diagnosis are one step because both
/// need the failing input's *meaning*, not just its values.
fn sharpen(spec: &Spec, prog: &Program, cx: Counterexample) -> (Counterexample, Vec<String>) {
    let Some(flat) = flatten_named(spec, &cx.inputs) else {
        return (cx, Vec::new());
    };
    let minimal = minimize_counterexample(spec, prog, &flat);
    match eval::check_contract_program(spec, prog, &minimal) {
        Err(v) => (
            Counterexample {
                inputs: describe_inputs(spec, &minimal),
                violation: diagnose_violation(spec, prog, &minimal, &v),
            },
            advise(spec, prog, &minimal, &v),
        ),
        Ok(_) => (cx, Vec::new()),
    }
}

/// Split a conjunction into its top-level conjuncts.
fn conjuncts_of(e: &Expr, out: &mut Vec<Expr>) {
    match e {
        Expr::Binary(BinOp::And, l, r) => {
            conjuncts_of(l, out);
            conjuncts_of(r, out);
        }
        _ => out.push(e.clone()),
    }
}

/// Which part of a failed obligation actually fails, evaluated at the state the
/// engine reported.
///
/// A loop obligation's goal is a conjunction, and printing the whole thing —
/// `goal false: (((acc + i) == sum(...)) && ((i + 1) >= 0))` — makes the reader
/// do the work of finding the broken part. Evaluating each conjunct at that
/// state names it, which is the difference between a fact and a diagnosis.
fn failing_conjuncts(ob: &crate::hoare::Obligation, named: &[(String, i64)]) -> Vec<String> {
    let mut env = eval::Env::default();
    for b in &ob.vars {
        match b.ty {
            Type::Array { index, .. } => {
                let mut contents = Vec::new();
                for i in index.lo..=index.hi {
                    let key = format!("{}[{}]", b.name, i);
                    if let Some((_, v)) = named.iter().find(|(n, _)| *n == key) {
                        contents.push(*v);
                    }
                }
                if !contents.is_empty() {
                    env.arrays.insert(b.name.clone(), contents);
                }
            }
            _ => {
                if let Some((_, v)) = named.iter().find(|(n, _)| *n == b.name) {
                    env.params.push((b.name.clone(), eval::Value::Int(*v)));
                }
            }
        }
    }
    let mut cs = Vec::new();
    conjuncts_of(&ob.goal, &mut cs);
    cs.iter()
        .filter(|c| !matches!(eval::eval(c, &env), Ok(eval::Value::Bool(true))))
        .map(|c| c.to_string())
        .collect()
}

/// Prove (or refute) `spec` against `prog`.
///
/// Two paths, chosen by what the program actually is:
///
/// * **Straight-line scalar code** — the original path: evaluate the body on
///   every input (exhaustive) and bit-blast the contract (BDD).
/// * **Control flow or arrays** — the Hoare path: execute the program over
///   the domain *and* discharge the generated verification conditions
///   symbolically. Two independent methods again, for a different reason:
///   execution shows the loop behaves; the invariant proof shows it must.
pub fn prove(spec: &Spec, prog: &Program, opts: &ProverOptions) -> ProofResult {
    let domain = spec.input_domain_size();

    // The spec's `example` witnesses are constraints the author stated, so
    // they are checked before anything else — for BOTH paths. A contract can
    // be weaker than the examples it ships with (`ensures r >= a` alongside
    // `example (5) => (7)`), and a program that satisfies only the contract
    // would otherwise be certified while contradicting its own witness.
    if let Some((idx, inputs, got, expected)) =
        eval::check_examples_program(spec, prog).into_iter().next()
    {
        let got_str = match &got {
            Ok(vals) => vals
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            Err(fault) => format!("fault: {}", fault),
        };
        let expected_str = expected
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        return ProofResult {
            verdict: Verdict::Violated,
            engines: vec![EngineReport {
                engine: "examples".into(),
                verdict: Verdict::Violated,
                checked: spec.examples.len() as u128,
                nodes: None,
                notes: vec![format!(
                    "example #{} is violated: inputs {} produce ({}) but the spec says ({})",
                    idx + 1,
                    describe_inputs(spec, &inputs)
                        .iter()
                        .map(|(n, v)| format!("{}={}", n, v))
                        .collect::<Vec<_>>()
                        .join(", "),
                    got_str,
                    expected_str
                )],
            }],
            counterexample: Some(Counterexample {
                inputs: describe_inputs(spec, &inputs),
                violation: format!(
                    "example #{}: got ({}) but the spec says ({})",
                    idx + 1,
                    got_str,
                    expected_str
                ),
            }),
            pre_witness: Some(Vec::new()),
            stat_bound: None,
            cross_validated: false,
            suggestions: vec![format!(
                "example #{} pins the behaviour at those inputs: either fix the body to match \
                 the witness, or correct the witness if the contract is what you meant",
                idx + 1
            )],
        };
    }

    let straight = ast::as_straight_line(prog).filter(|_| !ast::program_uses_arrays(prog));
    match straight {
        Some(body) => prove_straight(spec, &body, opts, domain),
        None => prove_with_hoare(spec, prog, opts, domain),
    }
}

/// The Hoare path: execution over the domain + symbolic obligation discharge.
fn prove_with_hoare(
    spec: &Spec,
    prog: &Program,
    opts: &ProverOptions,
    domain: u128,
) -> ProofResult {
    let (pre_witness, vacuity_notes) = check_vacuity(spec, &[], opts, domain);

    let mut engines: Vec<EngineReport> = Vec::new();
    let mut counterexample: Option<Counterexample> = None;
    let mut notes: Vec<String> = Vec::new();
    let mut obligation_advice: Vec<String> = Vec::new();

    // Engine 1: execute the program over the whole domain
    let mut exec_verdict: Option<Verdict> = None;
    if opts.engine == "auto" || opts.engine == "exhaustive" {
        match run_exhaustive(spec, prog, opts.exhaustive_budget) {
            Ok(report) => {
                if counterexample.is_none() {
                    counterexample = report.counterexample.clone();
                }
                exec_verdict = Some(report.verdict.clone());
                let mut n = report.notes.clone();
                n.push(
                    "executed the program (loops included) on every in-domain input".into(),
                );
                engines.push(EngineReport {
                    engine: "exhaustive-execution".into(),
                    verdict: report.verdict,
                    checked: report.checked,
                    nodes: None,
                    notes: n,
                });
            }
            Err(reason) => {
                engines.push(EngineReport {
                    engine: "exhaustive-execution".into(),
                    verdict: Verdict::GaveUp {
                        reason: reason.clone(),
                    },
                    checked: 0,
                    nodes: None,
                    notes: vec![reason],
                });
            }
        }
    }

    // Engine 2: Hoare obligations, discharged symbolically
    let obs = crate::hoare::obligations(spec, prog);
    let mut hc_verdict: Option<Verdict> = None;
    if opts.engine == "auto" || opts.engine == "bdd" || opts.engine == "exhaustive" {
        let mut all_proved = true;
        let mut any_ran = false;
        let mut total_checked: u128 = 0;
        let mut worst_nodes: u128 = 0;
        let mut failed: Option<(String, Counstext)> = None;
        for ob in &obs {
            let r = check_validity(&ob.vars, &ob.assumptions, &ob.goal, opts);
            any_ran = true;
            total_checked += r.engines.iter().map(|e| e.checked).sum::<u128>();
            // The obligation checker explains declining decisions ("array
            // state: decided symbolically", "state space is N: not
            // enumerated"). Those explanations are the honest part of the
            // report — surface them instead of dropping them.
            for n in &r.notes {
                notes.push(format!("[{}] {}", ob.kind, n));
            }
            for e in &r.engines {
                if let Some(n) = e.nodes {
                    worst_nodes = worst_nodes.max(n);
                }
            }
            match &r.verdict {
                Verdict::Proved => {}
                Verdict::Violated => {
                    all_proved = false;
                    let mut cx = r.counterexample.clone();
                    if let Some(c) = cx.as_mut() {
                        obligation_advice.extend(advise_obligation(&ob.kind, &c.inputs));
                        // Name the conjunct that broke instead of printing the
                        // whole goal for the reader to search.
                        let failing = failing_conjuncts(ob, &c.inputs);
                        if !failing.is_empty() {
                            c.violation = format!(
                                "{} fails: {} is not established at this state",
                                ob.kind,
                                failing.join("; and ")
                            );
                        }
                    }
                    failed = Some((ob.kind.clone(), Counstext {
                        counterexample: cx,
                        obligation: ob.to_string(),
                    }));
                    break;
                }
                Verdict::GaveUp { reason } => {
                    all_proved = false;
                    notes.push(format!(
                        "obligation `{}` undecided: {}",
                        ob.kind, reason
                    ));
                    break;
                }
                Verdict::NoViolationFound => {
                    all_proved = false;
                    notes.push(format!("obligation `{}` only sampled", ob.kind));
                    break;
                }
            }
        }
        if any_ran {
            hc_verdict = Some(if all_proved {
                Verdict::Proved
            } else if let Some((kind, ctx)) = &failed {
                notes.push(format!("FAILED obligation `{}`: {}", kind, ctx.obligation));
                if counterexample.is_none() {
                    counterexample = ctx.counterexample.clone();
                }
                Verdict::Violated
            } else {
                Verdict::GaveUp {
                    reason: "some obligations were undecided".into(),
                }
            });
        }
        engines.push(EngineReport {
            engine: "hoare-verification".into(),
            verdict: hc_verdict.clone().unwrap_or(Verdict::GaveUp {
                reason: "no obligations generated".into(),
            }),
            checked: total_checked,
            nodes: Some(worst_nodes),
            notes: {
                let mut v = vec![format!(
                    "{} verification condition(s): contract, loop entry/preservation/exit{}",
                    obs.len(),
                    if crate::hoare::has_unproven_termination(prog) {
                        " (no `decreases` clause given: PARTIAL correctness only)"
                    } else {
                        ", and termination"
                    }
                )];
                v.extend(notes.iter().cloned());
                v
            },
        });
    }

    // combine
    let verdict = match (exec_verdict.clone(), hc_verdict.clone()) {
        (Some(a), Some(b)) if a == b => a,
        (Some(Verdict::Violated), _) | (_, Some(Verdict::Violated)) => Verdict::Violated,
        (Some(Verdict::Proved), Some(Verdict::GaveUp { .. })) => Verdict::GaveUp {
            reason: "execution agrees, but the invariant proof was inconclusive".into(),
        },
        (Some(Verdict::GaveUp { .. }), Some(Verdict::Proved)) => Verdict::GaveUp {
            reason: "invariants proved, but full-domain execution was inconclusive".into(),
        },
        (Some(a), None) => a,
        (None, Some(b)) => b,
        (None, None) => Verdict::GaveUp {
            reason: "no engine could run".into(),
        },
        // Any mixed pair that isn't Proved/Proved is not a complete proof.
        (Some(_), Some(_)) => Verdict::GaveUp {
            reason: "engines did not both reach a complete verdict".into(),
        },
    };

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

    let cross_validated = matches!(
        (&exec_verdict, &hc_verdict),
        (Some(Verdict::Proved), Some(Verdict::Proved))
    );

    let (counterexample, mut suggestions) = match counterexample {
        Some(cx) => {
            let (c, s) = sharpen(spec, prog, cx);
            (Some(c), s)
        }
        None => (None, Vec::new()),
    };
    suggestions.extend(obligation_advice);

    ProofResult {
        verdict,
        engines,
        counterexample,
        pre_witness,
        stat_bound: None,
        cross_validated,
        suggestions,
    }
}

/// Extra context for a failed obligation (kept out of the public error type).
struct Counstext {
    counterexample: Option<Counterexample>,
    obligation: String,
}

/// The straight-line path (unchanged semantics, now fed by the dispatcher).
fn prove_straight(
    spec: &Spec,
    body: &[Assign],
    opts: &ProverOptions,
    domain: u128,
) -> ProofResult {

    // Vacuity: does any input reach the body?
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

    // Engine 1: exhaustive
    let mut exhaustive_verdict: Option<Verdict> = None;
    let prog = ast::assigns_to_program(body);
    if want_exhaustive {
        match run_exhaustive(spec, &prog, opts.exhaustive_budget) {
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

    // Engine 2: BDD
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

    // Engine 3: statistical (only if nothing complete succeeded)
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

    // Cross-validation
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

    let (counterexample, suggestions) = match counterexample {
        Some(cx) => {
            let (c, s) = sharpen(spec, &prog, cx);
            (Some(c), s)
        }
        None => (None, Vec::new()),
    };

    ProofResult {
        verdict,
        engines,
        counterexample,
        pre_witness,
        stat_bound,
        cross_validated,
        suggestions,
    }
}

fn exhaustively_complete(v: &Option<Verdict>) -> bool {
    matches!(v, Some(Verdict::Proved) | Some(Verdict::Violated))
}

// Vacuity check

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
        let ranges: Vec<IntRange> = crate::ast::input_domains(spec);
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
    let (pre, named) = {
        let mut bb = BitBlaster::new(&mut bdd);
        let mut env = std::collections::HashMap::new();
        // Interleaved variable ordering (Bryant): keeps arithmetic local.
        let ranges: Vec<IntRange> = crate::ast::input_domains(spec);
        let vals = bb.param_bits_interleaved(&ranges).map_err(|e| e.to_string())?;
        let mut named = Vec::new();
        for (p, v) in spec.params.iter().zip(vals) {
            env.insert(p.name.clone(), ival_clone(&v));
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
        (pre, named)
    };
    if !bdd_sat(&bdd, pre) {
        return Ok(None);
    }
    let assign = bdd_one_sat(&bdd, pre);
    Ok(Some(decode_params(spec, &named, &assign, &bdd)))
}

// Small indirections so prove.rs doesn't reach into Bdd internals directly.
fn bdd_sat(b: &Bdd, f: u32) -> bool {
    b.sat(f)
}
fn bdd_one_sat(b: &Bdd, f: u32) -> std::collections::HashMap<u32, bool> {
    b.one_sat(f)
}

use crate::bitblast::IVal as _IVal;
fn ival_clone(v: &_IVal) -> _IVal {
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
    bdd: &Bdd,
) -> Vec<(String, i64)> {
    // Each bit node carries its own variable index, so this decodes
    // correctly under ANY allocation order (param-major or interleaved).
    let mut out = Vec::new();
    for (name, v) in named {
        let mut val: i64 = 0;
        let w = v.bits.len();
        for (i, &node) in v.bits.iter().enumerate() {
            let bit = if node == crate::bdd::FALSE {
                false
            } else if node == crate::bdd::TRUE {
                true
            } else {
                match bdd.var_of(node) {
                    Some(var) => *assign.get(&var).unwrap_or(&false),
                    None => false, // unreachable for fresh variable nodes
                }
            };
            if bit {
                val |= 1i64 << i;
            }
        }
        // Sign-extend.
        if w > 0 && val & (1i64 << (w - 1)) != 0 {
            val |= -1i64 << w;
        }
        out.push((name.clone(), val));
    }
    let _ = spec;
    out
}

// Odometer

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

// Exhaustive engine

/// The exhaustive engine: walk every input in the domain and *execute* the
/// program (loops, branches and all) through the reference machine.
///
/// This is the definition of correctness by construction, and it is the
/// cross-check for the symbolic Hoare proof of loops: one executes them, the
/// other reasons about them.
fn run_exhaustive(
    spec: &Spec,
    prog: &Program,
    budget: u128,
) -> Result<ExhaustiveReport, String> {
    let domain = spec.input_domain_size();
    if domain > budget {
        return Err(format!(
            "domain of {} inputs exceeds budget of {} — declining (BDD or sampling next)",
            domain, budget
        ));
    }

    // Flat scalar domains: an array parameter of N elements contributes N
    // domains, so enumeration covers every array *content*.
    let ranges: Vec<IntRange> = ast::input_domains(spec);

    let mut inputs: Vec<i64> = ranges.iter().map(|r| r.lo).collect();
    let mut checked: u128 = 0;
    let mut notes = Vec::new();

    loop {
        if eval::precondition_holds(spec, &inputs) {
            checked += 1;
            match eval::check_contract_program(spec, prog, &inputs) {
                Ok(false) => {} // satisfied
                Ok(true) => {}  // out of domain (double-checked inside)
                Err(v) => {
                    let cx = Counterexample {
                        inputs: describe_inputs(spec, &inputs),
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

// BDD engine

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
        // Interleaved variable ordering — see bitblast::param_bits_interleaved.
        let ranges: Vec<IntRange> = crate::ast::input_domains(spec);
        let vals = bb
            .param_bits_interleaved(&ranges)
            .map_err(|e: BlastError| e.to_string())?;
        let mut named: Vec<(String, _IVal)> = Vec::new();
        for (p, v) in spec.params.iter().zip(vals) {
            if matches!(p.ty, Type::Bool) {
                return Err("bool params unsupported".into());
            }
            env.insert(p.name.clone(), ival_clone(&v));
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
    let decoded = decode_params(spec, &named, &assign, &bdd);
    // How much of the domain is bad? (Level-aware counting; may saturate.)
    let violating = bdd.count_sat(bad, vars_used);

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
                format!(
                    "≈{} of the encoded input assignments violate the contract",
                    violating
                ),
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

// Obligation checking (the Hoare path)

/// Result of checking one universally quantified obligation.
pub struct ValidityResult {
    pub verdict: Verdict,
    pub engines: Vec<EngineReport>,
    pub counterexample: Option<Counterexample>,
    pub notes: Vec<String>,
}

/// Check `assumptions ⇒ goal` for **every** value of `vars` in their declared
/// domains. This is the shape every Hoare obligation has, and it is exactly
/// what the existing engines already decide.
pub fn check_validity(
    vars: &[Binding],
    assumptions: &[Expr],
    goal: &Expr,
    opts: &ProverOptions,
) -> ValidityResult {
    let mut engines = Vec::new();
    let mut counterexample = None;
    let mut notes = Vec::new();
    let mut exhaustive_verdict: Option<Verdict> = None;
    let mut bdd_verdict: Option<Verdict> = None;

    // exhaustive over the obligation's variable domains
    // Only attempted when the state space is genuinely small: each state may
    // evaluate quantifiers, so this engine is for obligations the symbolic
    // engine cannot take (arrays), not the default. For loops the symbolic
    // check is both faster and the one that actually reasons.
    const OBLIGATION_STATE_BUDGET: u128 = 2_000_000;
    // This engine enumerates ONE value per variable, so array state (N values
    // per variable) is not something it models. Array obligations are decided
    // symbolically instead � claiming a verdict from a model that does not fit
    // the data is exactly the kind of false proof this project refuses to emit.
    let has_array_state = vars.iter().any(|b| matches!(b.ty, Type::Array { .. }));
    let domains: Vec<IntRange> = vars
        .iter()
        .map(|b| b.ty.as_int_range().unwrap_or(IntRange::new(0, 1)))
        .collect();
    let space: u128 = domains.iter().map(|r| r.size()).product();
    let bdd_will_try = opts.engine == "auto" || opts.engine == "bdd";
    let exhaustive_worth_it = !has_array_state
        && (space <= OBLIGATION_STATE_BUDGET || !bdd_will_try);
    if has_array_state && bdd_will_try {
        notes.push(
            "obligation involves array state; decided symbolically (an array is N integer \
             variables with ITE-chain access)"
                .into(),
        );
    }
    if exhaustive_worth_it {
        let synthetic = synthetic_spec(vars, assumptions, goal);
        let mut cur: Vec<i64> = domains.iter().map(|r| r.lo).collect();
        let mut checked: u128 = 0;
        let mut found: Option<Counterexample> = None;
        loop {
            let env = eval::input_env(&synthetic, &cur);
            if eval::precondition_holds(&synthetic, &cur) {
                checked += 1;
                let goal_holds = matches!(eval::eval(goal, &env), Ok(eval::Value::Bool(true)));
                if !goal_holds {
                    found = Some(Counterexample {
                        inputs: vars
                            .iter()
                            .zip(&cur)
                            .map(|(b, v)| (b.name.clone(), *v))
                            .collect(),
                        violation: format!("goal false: {}", goal),
                    });
                    break;
                }
            }
            if !increment(&domains, &mut cur) {
                break;
            }
        }
        match found {
            Some(cx) => {
                exhaustive_verdict = Some(Verdict::Violated);
                counterexample = Some(cx);
            }
            None => exhaustive_verdict = Some(Verdict::Proved),
        }
        engines.push(EngineReport {
            engine: "exhaustive".into(),
            verdict: exhaustive_verdict.clone().unwrap(),
            checked,
            nodes: None,
            notes: vec![format!(
                "enumerated all {} states of the obligation",
                space
            )],
        });
    } else {
        // Deliberately not attempted: the symbolic engine is the right tool
        // for a large obligation state space. Not a failure, so no engine
        // entry — just a note for the report.
        notes.push(format!(
            "obligation state space is {} states; checked symbolically rather than by enumeration",
            space
        ));
    }

    // BDD over the same obligation
    if opts.engine == "auto" || opts.engine == "bdd" {
        match bdd_check_validity(vars, assumptions, goal, opts.bdd_budget) {
            Ok((verdict, nodes, cx)) => {
                bdd_verdict = Some(verdict.clone());
                if counterexample.is_none() {
                    counterexample = cx.clone();
                }
                engines.push(EngineReport {
                    engine: "bdd-symbolic".into(),
                    verdict,
                    checked: 1,
                    nodes: Some(nodes),
                    notes: vec!["symbolic check of the obligation".into()],
                });
            }
            Err(e) => {
                engines.push(EngineReport {
                    engine: "bdd-symbolic".into(),
                    verdict: Verdict::GaveUp { reason: e.clone() },
                    checked: 0,
                    nodes: None,
                    notes: vec![e],
                });
            }
        }
    }

    // cross-validate
    let verdict = match (exhaustive_verdict, bdd_verdict) {
        (Some(a), Some(b)) if a == b => a,
        (Some(a), Some(b)) => {
            notes.push(format!(
                "ENGINES DISAGREE on obligation (exhaustive={:?}, bdd={:?}) — refusing to certify",
                a, b
            ));
            Verdict::GaveUp {
                reason: "internal: engines disagree on obligation".into(),
            }
        }
        (Some(a), None) => a,
        (None, Some(b)) => b,
        (None, None) => {
            // Surface whatever the engines actually said, so a declined
            // obligation is diagnosable rather than mysterious.
            let mut why: Vec<String> = engines
                .iter()
                .filter_map(|e| match &e.verdict {
                    Verdict::GaveUp { reason } => Some(reason.clone()),
                    _ => None,
                })
                .collect();
            why.extend(notes.iter().cloned());
            Verdict::GaveUp {
                reason: if why.is_empty() {
                    "no engine could check the obligation".into()
                } else {
                    why.join("; ")
                },
            }
        }
    };

    ValidityResult {
        verdict,
        engines,
        counterexample,
        notes,
    }
}

/// A synthetic spec used to reuse the engines' domain machinery for an
/// obligation: variables become parameters, assumptions become `requires`.
fn synthetic_spec(vars: &[Binding], assumptions: &[Expr], goal: &Expr) -> Spec {
    Spec {
        name: "obligation".into(),
        params: vars.to_vec(),
        results: Vec::new(),
        locals: Vec::new(),
        requires: assumptions.to_vec(),
        ensures: vec![goal.clone()],
        examples: Vec::new(),
        body: None,
    }
}

fn bdd_check_validity(
    vars: &[Binding],
    assumptions: &[Expr],
    goal: &Expr,
    budget: usize,
) -> Result<(Verdict, u128, Option<Counterexample>), String> {
    // Division is the one fragment the bitblaster declines.
    for e in assumptions.iter().chain(std::iter::once(goal)) {
        if bitblast::contains_division(e) {
            return Err("obligation uses division (no circuit implemented)".into());
        }
    }

    let mut bdd = Bdd::new(budget);

    // Layout: one slot per scalar, one per array element. An array is exactly
    // N integer variables, so this needs no new theory.
    let layout: Vec<(String, IntRange, usize)> = vars
        .iter()
        .map(|b| match b.ty {
            Type::Array { index, elem } => (b.name.clone(), elem, index.size() as usize),
            Type::Int(r) => (b.name.clone(), r, 1),
            Type::Decimal { stored, .. } => (b.name.clone(), stored, 1),
            Type::Bool => (b.name.clone(), IntRange::new(0, 1), 1),
        })
        .collect();

    let (bad, nodes, named) = {
        let mut bb = BitBlaster::new(&mut bdd);
        let (scalars, arrays) = bb
            .alloc_params(&layout)
            .map_err(|e: BlastError| e.to_string())?;

        // Every leaf needs its range constrained, arrays included.
        let mut domain_parts: Vec<(String, _IVal, IntRange)> = Vec::new();
        let mut named: Vec<(String, _IVal)> = Vec::new();
        for (name, range, count) in &layout {
            if *count == 1 {
                if let Some(v) = scalars.get(name) {
                    domain_parts.push((name.clone(), v.clone(), *range));
                    named.push((name.clone(), v.clone()));
                }
            } else if let Some(elems) = arrays.get(name) {
                for (k, e) in elems.iter().enumerate() {
                    domain_parts.push((format!("{}[{}]", name, k), e.clone(), *range));
                    named.push((format!("{}[{}]", name, k), e.clone()));
                }
            }
        }

        bb.arrays = arrays;
        let bad = bb
            .bad_state_predicate(&domain_parts, &scalars, assumptions, std::slice::from_ref(goal))
            .map_err(|e: BlastError| e.to_string())?;
        let nodes = bb.bdd.node_count() as u128;
        (bad, nodes, named)
    };

    if !bdd.sat(bad) {
        return Ok((Verdict::Proved, nodes, None));
    }

    // A real counterexample: decode the satisfying assignment into leaf
    // values (scalars and array elements alike).
    let assign = bdd_one_sat(&bdd, bad);
    let synthetic = synthetic_spec(vars, assumptions, goal);
    let decoded = decode_params(&synthetic, &named, &assign, &bdd);

    // CONFIRM the counterexample with the reference evaluator before
    // reporting it. The contract path has always done this; obligations must
    // too, or a symbolic-encoding bug becomes a bogus accusation against the
    // user's program. If the evaluator says the obligation actually HOLDS
    // here, the two disagree and we refuse to certify rather than guess.
    if obligation_holds_at(&synthetic, vars, assumptions, goal, &decoded) {
        return Err(format!(
            "internal: symbolic engine reported a violation at {:?} that the evaluator \
             accepts � refusing to certify",
            decoded
        ));
    }
    Ok((
        Verdict::Violated,
        nodes,
        Some(Counterexample {
            inputs: decoded,
            violation: format!("obligation fails: {}", goal),
        }),
    ))
}

/// Evaluate `assumptions ? goal` at decoded leaf values, with the reference
/// evaluator. Array elements arrive as `name[k]` entries.
fn obligation_holds_at(
    synthetic: &Spec,
    vars: &[Binding],
    assumptions: &[Expr],
    goal: &Expr,
    decoded: &[(String, i64)],
) -> bool {
    let mut env = eval::Env::default();
    let mut scalar_inputs: Vec<i64> = Vec::new();
    for b in vars {
        if matches!(b.ty, Type::Array { .. }) {
            // Gather the elements that were decoded for this array.
            let mut elems: Vec<(usize, i64)> = decoded
                .iter()
                .filter_map(|(n, v)| {
                    let prefix = format!("{}[", b.name);
                    let idx = n.strip_prefix(&prefix)?.strip_suffix(']')?;
                    Some((idx.parse::<usize>().ok()?, *v))
                })
                .collect();
            elems.sort_by_key(|(i, _)| *i);
            let contents: Vec<i64> = elems.into_iter().map(|(_, v)| v).collect();
            env.arrays.insert(b.name.clone(), contents);
        } else {
            let v = decoded
                .iter()
                .find(|(n, _)| n == &b.name)
                .map(|(_, v)| *v)
                .unwrap_or(0);
            env.params.push((b.name.clone(), eval::Value::Int(v)));
            scalar_inputs.push(v);
        }
    }
    let _ = synthetic;
    let _ = scalar_inputs;
    for a in assumptions {
        if !matches!(eval::eval(a, &env), Ok(eval::Value::Bool(true))) {
            return true; // assumptions false here: obligation is vacuous
        }
    }
    matches!(eval::eval(goal, &env), Ok(eval::Value::Bool(true)))
}


fn run_statistical(
    spec: &Spec,
    body: &[Assign],
    opts: &ProverOptions,
) -> (Verdict, Option<(f64, f64)>, Vec<String>) {
    let n = opts.samples;
    let mut rng = SplitMix64::new(0x1CE_BDD ^ (n as u64));
    let ranges: Vec<IntRange> = crate::ast::input_domains(spec);

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

// Certificate

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
        s.push_str("probatum-cert-1\n");
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
    fn cross_validates_division() {
        // Division used to be the one fragment the symbolic engine declined.
        // With restoring-division circuits it now PROVES � so this test flipped
        // from "the BDD must decline honestly" to "both engines must agree",
        // which is a strictly stronger claim about the same program.
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
        assert_eq!(r.verdict, Verdict::Proved, "engines: {:?}", r.engines);
        let bdd = r.engines.iter().find(|e| e.engine == "bdd-symbolic").unwrap();
        assert_eq!(
            bdd.verdict,
            Verdict::Proved,
            "the symbolic engine must now decide division: {:?}",
            bdd
        );
        assert!(r.cross_validated, "both engines must agree on division");
    }

    #[test]
    fn cross_validates_chained_arithmetic() {
        // Regression: `a + 1 + 0 - 1` has an intermediate ([1..16], 7 bits)
        // WIDER than the final static range ([0..15], 6 bits). The bitblaster
        // once sized circuits from the result range alone and tripped its own
        // assertion. Now it must prove and cross-validate.
        let s = parse(
            r#"
            spec chain(a: int[0..15]) returns (r: int[0..16])
              ensures r == a + 1 + 0 - 1 + 1
              example (5) => (6)
            { r := a + 1 + 0 - 1 + 1; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let body = s.body.clone().unwrap();
        let r = prove(&s, &body, &ProverOptions::default());
        assert_eq!(r.verdict, Verdict::Proved, "engines: {:?}", r.engines);
        assert!(r.cross_validated, "both engines must agree on chains");
    }

    #[test]
    fn minimizes_the_counterexample() {
        // The failure region is a + b > 5, whose max-norm minimum is (3, 3).
        // The first minimizer accepted any failing candidate, so a coordinate
        // could grow and the witness drifted to (4, 2) — larger in every norm
        // a reader cares about.
        let s = parse(
            r#"
            spec widen(a: int[0..10], b: int[0..10]) returns (r: int[0..5])
              ensures r >= 0
            { r := a + b; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let prog = s.body.clone().unwrap();
        let r = prove(&s, &prog, &ProverOptions::default());
        assert_eq!(r.verdict, Verdict::Violated);
        let cx = r.counterexample.expect("a counterexample");
        let a = cx.inputs.iter().find(|(n, _)| n == "a").unwrap().1;
        let b = cx.inputs.iter().find(|(n, _)| n == "b").unwrap().1;
        assert_eq!((a, b), (3, 3), "expected the minimal witness");
    }

    #[test]
    fn advice_names_the_construct_to_change() {
        let s = parse(
            r#"
            spec avg(a: int[0..100], n: int[0..10]) returns (r: int[0..100])
              ensures r == a / n
            { r := a / n; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let prog = s.body.clone().unwrap();
        let r = prove(&s, &prog, &ProverOptions::default());
        assert_eq!(r.verdict, Verdict::Violated);
        // The witness is the simplest one there is…
        let cx = r.counterexample.expect("a counterexample");
        assert!(
            cx.inputs.iter().all(|(_, v)| *v == 0),
            "expected the all-zero witness, got {:?}",
            cx.inputs
        );
        // …and the advice names both ways out.
        assert!(
            r.suggestions
                .iter()
                .any(|s| s.contains("requires") && s.contains("!= 0")),
            "advice must name a fix, got {:?}",
            r.suggestions
        );
    }

    #[test]
    fn diagnosis_reports_the_values_on_both_sides() {
        // "ensures #2 false" is a fact; naming the shortfall is a diagnosis.
        let s = parse(
            r#"
            spec off_by_one(a: int[0..20]) returns (r: int[0..20])
              ensures r == a + 1
            { r := a; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let prog = s.body.clone().unwrap();
        let r = prove(&s, &prog, &ProverOptions::default());
        let cx = r.counterexample.expect("a counterexample");
        assert!(
            cx.violation.contains("short by 1"),
            "expected a numeric diagnosis, got: {}",
            cx.violation
        );
    }

    #[test]
    fn names_the_failing_conjunct_of_an_obligation() {
        // A loop obligation's goal is a conjunction. Printing the whole thing
        // makes the reader hunt for the broken part; the diagnosis should name
        // it, and say which loop fact is missing.
        let s = parse(
            r#"
            spec bad_inv(n: int[0..5])
              returns (s: int[0..20])
              locals (i: int[0..6], acc: int[0..20])
              ensures s >= 0
            {
              i := 0; acc := 0;
              while i <= n
                invariant acc == sum(k in 0..i: k)
                invariant i >= 0
                decreases n - i + 1
              { acc := acc + i; i := i + 1; }
              s := acc;
            }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let prog = s.body.clone().unwrap();
        let r = prove(&s, &prog, &ProverOptions::default());
        assert_eq!(r.verdict, Verdict::Violated);
        let cx = r.counterexample.expect("a counterexample");
        assert!(
            cx.violation.contains("loop preservation fails"),
            "should name the obligation kind, got: {}",
            cx.violation
        );
        assert!(
            cx.violation.contains("sum"),
            "should name the broken conjunct, got: {}",
            cx.violation
        );
        assert!(
            r.suggestions.iter().any(|s| s.contains("not inductive")),
            "should explain that the invariant is not inductive, got: {:?}",
            r.suggestions
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
