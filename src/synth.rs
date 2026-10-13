//! The synthesizer: turn behavioral intent into a program.
//!
//! ## Strategy ladder (first success wins, all verified by the prover)
//!
//! 1. **Definitional extraction.** If `ensures` says `x == e` for
//!    param-only `e`, then `x := e` *is* the answer — the spec handed us
//!    the program. Chains (`y == f(x)` where `x` is itself defined)
//!    resolve by transitive substitution; cycles are reported honestly.
//!
//! 2. **Enumerative search (typed, observational-equivalence pruned).**
//!    Grow candidate expressions by increasing size over a typed grammar
//!    (int and bool sorts, `if`, `min`/`max`, arithmetic, comparisons).
//!    Candidates are filtered against accumulated examples and deduplicated
//!    by their *behavior on a sample* — structurally different but
//!    observationally identical candidates collapse to one, which is what
//!    keeps the search space from exploding.
//!
//! 3. **Counterexample-guided refinement (the CEGIS loop).** A candidate
//!    that passes every example is handed to the prover. If the prover
//!    refutes it, we take its counterexample input and *solve for a valid
//!    output* at that input by bounded enumeration over the declared result
//!    domains (checking every `ensures` clause). The new witness joins the
//!    example set and the search resumes — strictly smarter than before.
//!
//! ## What failure means
//!
//! * Search-space exhaustion ⇒ "no program of size ≤ N found" — NOT a proof
//!   that none exists. Reported as such.
//! * Unrealizable input ⇒ a concrete input where *no* output tuple can
//!   satisfy the contract — the spec itself is broken. Reported with that
//!   input. This is a genuine impossibility proof about the spec.
//!
//! Everything the synthesizer emits still has to survive `prove::prove` —
//! synthesis never gets to bless its own output.

use crate::ast::*;
use crate::eval::{self, Value};
use crate::prove::{self, ProverOptions, Verdict};
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub enum SynthError {
    /// The spec's own examples contradict its clauses (spec bug).
    SpecInconsistent { message: String },
    /// Found an input where no output tuple can satisfy `ensures`.
    Unrealizable { inputs: Vec<(String, i64)>, message: String },
    /// Gave up: nothing in the bounded search space works.
    Exhausted { message: String },
    /// Cyclic definitional structure we can't order.
    Cycle { message: String },
}

impl SynthError {
    /// When synthesis proves the *spec itself* is impossible, this is the
    /// input where no output can satisfy the contract. Callers surface it.
    pub fn unrealizable_input(&self) -> Option<&[(String, i64)]> {
        match self {
            SynthError::Unrealizable { inputs, .. } => Some(inputs),
            _ => None,
        }
    }
}

impl std::fmt::Display for SynthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SynthError::SpecInconsistent { message } | SynthError::Exhausted { message } | SynthError::Cycle { message } => f.write_str(message),
            SynthError::Unrealizable { message, .. } => f.write_str(message),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SynthStats {
    pub strategy: String,
    pub candidates_generated: u64,
    pub candidates_pruned: u64,
    pub examples_used: usize,
    pub cegis_rounds: usize,
    pub prover_refutations: usize,
}

#[derive(Debug)]
pub struct Synthesis {
    pub body: Vec<Assign>,
    pub stats: SynthStats,
}

const MAX_SIZE: usize = 6;
const MAX_CANDIDATES: u64 = 300_000;
const SAMPLE_INPUTS: usize = 24;
const MAX_REALIZABILITY_PRODUCT: u128 = 262_144; // 2^18 output tuples
/// Signature value for "this candidate faults here" — distinct from any
/// real value, since domains are bounded well above i64::MIN.
const FAULT_MARKER: i64 = i64::MIN;

/// Synthesize + prove a program for `spec`.
pub fn synthesize(spec: &Spec, opts: &ProverOptions) -> Result<Synthesis, SynthError> {
    validate_examples(spec)?;

    let mut examples: Vec<Example> = spec.examples.clone();
    let mut stats = SynthStats {
        strategy: String::new(),
        candidates_generated: 0,
        candidates_pruned: 0,
        examples_used: examples.len(),
        cegis_rounds: 0,
        prover_refutations: 0,
    };

    // Observational sample inputs: examples first, then deterministic extras.
    let sample_inputs = build_sample_inputs(spec, &examples);

    let definitional = extract_definitions(spec)?;

    let mut cegis_round = 0;
    loop {
        cegis_round += 1;
        stats.cegis_rounds = cegis_round;

        // ---- cover the remaining results --------------------------------
        let mut assigns: Vec<Assign> = Vec::new();
        let mut missing: Vec<String> = Vec::new();
        for r in &spec.results {
            if let Some(e) = definitional.get(&r.name) {
                assigns.push(Assign {
                    name: r.name.clone(),
                    value: e.clone(),
                });
            } else {
                missing.push(r.name.clone());
            }
        }

        if !missing.is_empty() {
            stats.strategy = if definitional.is_empty() {
                "enumerative".into()
            } else {
                "definitional+enumerative".into()
            };
            for name in &missing {
                let idx = spec.result_index(name).expect("checked");
                let cand = enumerate_result(
                    spec,
                    &examples,
                    idx,
                    &sample_inputs,
                    &mut stats,
                )?;
                assigns.push(Assign {
                    name: name.clone(),
                    value: cand,
                });
            }
        } else {
            stats.strategy = "definitional".into();
        }

        // Restore declaration order (parser/prover assume this).
        let mut body: Vec<Assign> = Vec::new();
        for r in &spec.results {
            let a = assigns
                .iter()
                .find(|a| a.name == r.name)
                .expect("every result covered");
            body.push(a.clone());
        }

        // Semantic sanity (the static analyzer's own eyes).
        if let Err(e) = crate::sema::analyze_with_body(spec, &body) {
            return Err(SynthError::Exhausted {
                message: format!("candidate failed semantic analysis: {}", e),
            });
        }

        // Examples must hold before we bother the prover.
        if let Some(bad) = eval::check_examples(spec, &body).into_iter().next() {
            // Fall through to prover-free refinement: this candidate can't
            // be right; if its values at example inputs are usable we still
            // need a new candidate — the enumerator already filters on
            // examples, so reaching here means definitional parts disagree
            // with examples ⇒ spec inconsistency (checked at extract time)
            // or a bug. Report honestly.
            return Err(SynthError::SpecInconsistent {
                message: format!(
                    "example #{} (inputs {:?}) expects {:?}, program produced {:?} — \
                     definitional clauses disagree with the witness",
                    bad.0, bad.1, bad.3, bad.2
                ),
            });
        }

        // ---- the moment of truth: the prover ----------------------------
        let proof = prove::prove(spec, &body, opts);
        match proof.verdict {
            Verdict::Proved => {
                return Ok(Synthesis { body, stats });
            }
            Verdict::Violated => {
                stats.prover_refutations += 1;
                let cx = proof.counterexample.ok_or_else(|| SynthError::Exhausted {
                    message: "prover reported violation without counterexample".into(),
                })?;
                // Solve for a valid output at the counterexample input.
                let inputs: Vec<i64> = spec
                    .params
                    .iter()
                    .map(|p| {
                        cx.inputs
                            .iter()
                            .find(|(n, _)| n == &p.name)
                            .map(|(_, v)| *v)
                            .unwrap_or(0)
                    })
                    .collect();
                match solve_outputs(spec, &inputs)? {
                    Some(outputs) => {
                        // New witness. If we've seen this input before, the
                        // candidate is chasing its tail — report exhaustion.
                        if examples.iter().any(|e| e.inputs == inputs) {
                            return Err(SynthError::Exhausted {
                                message: format!(
                                    "counterexample {:?} already witnessed; candidate keeps \
                                     producing contract-violating outputs — search space too \
                                     small (raise size bound)",
                                    cx.inputs
                                ),
                            });
                        }
                        examples.push(Example {
                            inputs,
                            outputs,
                        });
                        stats.examples_used = examples.len();
                        if cegis_round > 32 {
                            return Err(SynthError::Exhausted {
                                message: "CEGIS did not converge within 32 rounds".into(),
                            });
                        }
                        // Loop: re-extract (examples may pin down more) and re-enumerate.
                        continue;
                    }
                    None => {
                        let msg = format!(
                            "IMPOSSIBLE SPEC: at input {:?} no output tuple within the \
                             declared result domains satisfies every `ensures` clause — \
                             the contract cannot be met here (spec bug, not a synthesis failure)",
                            cx.inputs
                        );
                        return Err(SynthError::Unrealizable {
                            inputs: cx.inputs,
                            message: msg,
                        });
                    }
                }
            }
            Verdict::NoViolationFound => {
                return Err(SynthError::Exhausted {
                    message: "prover could not decide completely (only sampling ran)".into(),
                })
            }
            Verdict::GaveUp { reason } => {
                return Err(SynthError::Exhausted {
                    message: format!("prover gave up: {}", reason),
                })
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Example validation
// ---------------------------------------------------------------------------

fn validate_examples(spec: &Spec) -> Result<(), SynthError> {
    for (i, ex) in spec.examples.iter().enumerate() {
        if !eval::precondition_holds(spec, &ex.inputs) {
            return Err(SynthError::SpecInconsistent {
                message: format!(
                    "example #{}: inputs {:?} violate `requires` — a witness outside the \
                     contract domain cannot constrain the program",
                    i, ex.inputs
                ),
            });
        }
        // Plug (inputs, outputs) directly into ensures.
        let mut env = eval::input_env(spec, &ex.inputs);
        for (r, v) in spec.results.iter().zip(&ex.outputs) {
            env.results.push((r.name.clone(), Value::Int(*v)));
        }
        for (j, clause) in spec.ensures.iter().enumerate() {
            match eval::eval(clause, &env) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    return Err(SynthError::SpecInconsistent {
                        message: format!(
                            "example #{} (inputs {:?}) VIOLATES ensures #{}: {} — the spec's \
                             own witness contradicts its contract",
                            i, ex.inputs, j + 1, clause
                        ),
                    })
                }
                Ok(Value::Int(_)) => {
                    return Err(SynthError::SpecInconsistent {
                        message: format!("ensures #{} is not bool", j + 1),
                    })
                }
                Err(f) => {
                    return Err(SynthError::SpecInconsistent {
                        message: format!(
                            "example #{} faults evaluating ensures #{}: {}",
                            i,
                            j + 1,
                            f
                        ),
                    })
                }
            }
        }
        // Result domains.
        for (r, v) in spec.results.iter().zip(&ex.outputs) {
            if let Type::Int(range) = r.ty {
                if !range.contains(*v) {
                    return Err(SynthError::SpecInconsistent {
                        message: format!(
                            "example #{}: output {} for `{}` outside declared {}",
                            i, v, r.name, range
                        ),
                    });
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Definitional extraction
// ---------------------------------------------------------------------------

fn extract_definitions(spec: &Spec) -> Result<HashMap<String, Expr>, SynthError> {
    // Pass 1: direct `r == param-only` (either side). `r` may be written as
    // `result.r` or as a bare name (the parser produces Expr::Param for
    // bare identifiers; sema resolves them — here we check membership).
    let is_result = |name: &str| spec.results.iter().any(|b| b.name == name);
    let mut defs: HashMap<String, Expr> = HashMap::new();
    for clause in &spec.ensures {
        let (name, expr) = match clause {
            Expr::Binary(BinOp::Eq, l, r) => {
                let lhs_result = match &**l {
                    Expr::Result(n) => Some(n.clone()),
                    Expr::Param(n) if is_result(n) => Some(n.clone()),
                    _ => None,
                };
                let rhs_result = match &**r {
                    Expr::Result(n) => Some(n.clone()),
                    Expr::Param(n) if is_result(n) => Some(n.clone()),
                    _ => None,
                };
                match (lhs_result, rhs_result) {
                    (Some(n), None) => (n, (**r).clone()),
                    (None, Some(n)) => (n, (**l).clone()),
                    _ => continue, // both or neither: not a definition
                }
            }
            _ => continue,
        };
        if mentions_result(&expr) || mentions_bare_result(&expr, spec) {
            continue; // resolved in pass 2
        }
        // First definition wins; later duplicates are cross-checks the
        // prover will enforce.
        defs.entry(name).or_insert(expr);
    }

    // Pass 1b: piecewise definitions. `if c then (r == a) else (r == b)`
    // (with arbitrarily nested ifs) is a perfectly good definition of r:
    // r := if c then a else b. Real intent is full of these ("clamp",
    // "if valid then value else default"), so recognizing them turns whole
    // classes of specs from "enumeration required" into "extraction".
    for clause in &spec.ensures {
        if !matches!(clause, Expr::Ite(_, _, _)) {
            continue;
        }
        for r in &spec.results {
            if defs.contains_key(&r.name) {
                continue;
            }
            if let Some(e) = piecewise_definition(clause, &r.name, spec) {
                if !mentions_result(&e) && !mentions_bare_result(&e, spec) {
                    defs.insert(r.name.clone(), e);
                }
            }
        }
    }

    // Pass 2: transitively substitute defined results until fixpoint.
    for _ in 0..spec.results.len() + 1 {
        let snapshot: HashMap<String, Expr> = defs.clone();
        let mut changed = false;
        for (_, e) in defs.iter_mut() {
            let sub = subst_results_deep(e, &snapshot, spec);
            if sub != *e {
                *e = sub;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Any remaining result references ⇒ cycle or uncovered dependency.
    for (name, e) in &defs {
        if mentions_result(e) || mentions_bare_result(e, spec) {
            return Err(SynthError::Cycle {
                message: format!(
                    "definitional clause for `{}` references results that never reduce to \
                     parameters (cyclic definition): {}",
                    name, e
                ),
            });
        }
    }

    Ok(defs)
}

/// Does `e` mention any declared result by bare name?
fn mentions_bare_result(e: &Expr, spec: &Spec) -> bool {
    match e {
        Expr::Param(n) | Expr::Result(n) => spec.results.iter().any(|b| &b.name == n),
        Expr::Unary(_, a) => mentions_bare_result(a, spec),
        Expr::Binary(_, l, r) => mentions_bare_result(l, spec) || mentions_bare_result(r, spec),
        Expr::Ite(c, a, b) => {
            mentions_bare_result(c, spec)
                || mentions_bare_result(a, spec)
                || mentions_bare_result(b, spec)
        }
        Expr::Min(a, b) | Expr::Max(a, b) => {
            mentions_bare_result(a, spec) || mentions_bare_result(b, spec)
        }
        _ => false,
    }
}

/// Substitute both `result.r` and bare-result references.
fn subst_results_deep(e: &Expr, defs: &HashMap<String, Expr>, spec: &Spec) -> Expr {
    let is_result = |n: &str| spec.results.iter().any(|b| b.name == n);
    match e {
        Expr::Result(n) => defs.get(n).cloned().unwrap_or_else(|| e.clone()),
        Expr::Param(n) if is_result(n) => defs.get(n).cloned().unwrap_or_else(|| e.clone()),
        Expr::Unary(op, a) => Expr::Unary(*op, Box::new(subst_results_deep(a, defs, spec))),
        Expr::Binary(op, l, r) => Expr::Binary(
            *op,
            Box::new(subst_results_deep(l, defs, spec)),
            Box::new(subst_results_deep(r, defs, spec)),
        ),
        Expr::Ite(c, a, b) => Expr::Ite(
            Box::new(subst_results_deep(c, defs, spec)),
            Box::new(subst_results_deep(a, defs, spec)),
            Box::new(subst_results_deep(b, defs, spec)),
        ),
        Expr::Min(a, b) => Expr::Min(
            Box::new(subst_results_deep(a, defs, spec)),
            Box::new(subst_results_deep(b, defs, spec)),
        ),
        Expr::Max(a, b) => Expr::Max(
            Box::new(subst_results_deep(a, defs, spec)),
            Box::new(subst_results_deep(b, defs, spec)),
        ),
        _ => e.clone(),
    }
}

/// Recognize a piecewise definition of `result_name`:
/// `if c then (r == a) else (r == b)` ⇒ the expression `if c then a else b`.
/// Recurses through nested `if`s. Returns `None` when any branch doesn't
/// define `r` (then it isn't a definition, and we don't guess).
fn piecewise_definition(e: &Expr, result_name: &str, spec: &Spec) -> Option<Expr> {
    let defines = |x: &Expr| -> bool {
        matches!(x, Expr::Result(n) if n == result_name)
            || matches!(x, Expr::Param(n) if n == result_name && spec.results.iter().any(|b| b.name == *n))
    };
    match e {
        Expr::Binary(BinOp::Eq, l, r) => {
            if defines(l) && !mentions_named(r, result_name, spec) {
                Some((**r).clone())
            } else if defines(r) && !mentions_named(l, result_name, spec) {
                Some((**l).clone())
            } else {
                None
            }
        }
        Expr::Ite(c, a, b) => {
            let ra = piecewise_definition(a, result_name, spec)?;
            let rb = piecewise_definition(b, result_name, spec)?;
            Some(Expr::Ite(c.clone(), Box::new(ra), Box::new(rb)))
        }
        _ => None,
    }
}

/// Does `e` mention `name` as a result reference?
fn mentions_named(e: &Expr, name: &str, spec: &Spec) -> bool {
    match e {
        Expr::Result(n) | Expr::Param(n) => {
            n == name && spec.results.iter().any(|b| b.name == *n)
        }
        Expr::Unary(_, a) => mentions_named(a, name, spec),
        Expr::Binary(_, l, r) => mentions_named(l, name, spec) || mentions_named(r, name, spec),
        Expr::Ite(c, a, b) => {
            mentions_named(c, name, spec)
                || mentions_named(a, name, spec)
                || mentions_named(b, name, spec)
        }
        Expr::Min(a, b) | Expr::Max(a, b) => {
            mentions_named(a, name, spec) || mentions_named(b, name, spec)
        }
        _ => false,
    }
}

fn mentions_result(e: &Expr) -> bool {
    match e {
        Expr::Result(_) => true,
        Expr::Unary(_, a) => mentions_result(a),
        Expr::Binary(_, l, r) => mentions_result(l) || mentions_result(r),
        Expr::Ite(c, a, b) => mentions_result(c) || mentions_result(a) || mentions_result(b),
        Expr::Min(a, b) | Expr::Max(a, b) => mentions_result(a) || mentions_result(b),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Sample inputs (for observational pruning)
// ---------------------------------------------------------------------------

fn build_sample_inputs(spec: &Spec, examples: &[Example]) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = examples.iter().map(|e| e.inputs.clone()).collect();
    // Deterministic extras spread through the domain (SplitMix64 walk).
    let mut rng = crate::prove::SplitMix64::new(0x5EED_C0DE);
    let ranges: Vec<IntRange> = spec
        .params
        .iter()
        .map(|b| match b.ty {
            Type::Int(r) => r,
            Type::Bool => IntRange::new(0, 1),
        })
        .collect();
    let mut guard = 0;
    while out.len() < examples.len() + SAMPLE_INPUTS && guard < SAMPLE_INPUTS * 20 {
        guard += 1;
        let cand: Vec<i64> = ranges
            .iter()
            .map(|r| {
                let span = (r.hi - r.lo) as u64 + 1;
                r.lo + (rng.next() % span) as i64
            })
            .collect();
        if eval::precondition_holds(spec, &cand) && !out.contains(&cand) {
            out.push(cand);
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Enumerative search
// ---------------------------------------------------------------------------

/// Signature of a candidate: its value on every sample input (fault = i64::MIN).
type Signature = Vec<i64>;

fn enumerate_result(
    spec: &Spec,
    examples: &[Example],
    result_idx: usize,
    sample_inputs: &[Vec<i64>],
    stats: &mut SynthStats,
) -> Result<Expr, SynthError> {
    let result = &spec.results[result_idx];
    let (expected, bool_result) = match &result.ty {
        Type::Int(_) => (
            examples
                .iter()
                .map(|e| e.outputs[result_idx])
                .collect::<Vec<_>>(),
            false,
        ),
        Type::Bool => (
            // bool examples aren't representable in Example.outputs (ints);
            // bool results are constrained only by ensures — handled below
            // by the prover, so we filter on examples only when int.
            Vec::new(),
            true,
        ),
    };
    let _ = bool_result;

    // Grammar leaves.
    let literals = collect_literals(spec);
    let mut int_leaves: Vec<Expr> = spec
        .params
        .iter()
        .filter(|p| matches!(p.ty, Type::Int(_)))
        .map(|p| Expr::Param(p.name.clone()))
        .collect();
    for l in &literals {
        int_leaves.push(Expr::IntLit(*l));
    }

    // Layers by size. layer[size] = exprs of exactly that size.
    let mut int_layers: Vec<Vec<Expr>> = vec![Vec::new(); MAX_SIZE + 1];
    let mut bool_layers: Vec<Vec<Expr>> = vec![Vec::new(); MAX_SIZE + 1];

    // Size 1: leaves.
    int_layers[1] = int_leaves;
    bool_layers[1] = vec![Expr::BoolLit(true), Expr::BoolLit(false)];
    // Parameter comparisons as cheap bool seeds (size 3 conceptually, but
    // they're the workhorses of conditions — seed at 2 for reachability).
    let params: Vec<Expr> = spec
        .params
        .iter()
        .filter(|p| matches!(p.ty, Type::Int(_)))
        .map(|p| Expr::Param(p.name.clone()))
        .collect();
    for a in &params {
        for b in &params {
            for op in [BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge] {
                bool_layers[2].push(Expr::Binary(op, Box::new(a.clone()), Box::new(b.clone())));
            }
        }
        for l in &literals {
            for op in [BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge] {
                bool_layers[2].push(Expr::Binary(op, Box::new(a.clone()), Box::new(Expr::IntLit(*l))));
                bool_layers[2].push(Expr::Binary(op, Box::new(Expr::IntLit(*l)), Box::new(a.clone())));
            }
        }
    }

    // Seen-signature sets per sort.
    let mut seen_int: HashSet<Signature> = HashSet::new();
    let mut seen_bool: HashSet<Signature> = HashSet::new();
    // Acceptance: the candidate must match every example output at this index.
    let accepts = |e: &Expr| -> bool {
        if examples.is_empty() {
            return true; // no witnesses: rely on the prover
        }
        for (i, ex) in examples.iter().enumerate() {
            let env = eval::input_env(spec, &ex.inputs);
            let v = match eval::eval(e, &env) {
                Ok(v) => v,
                Err(_) => return false, // faults on a witness — reject
            };
            match v {
                Value::Int(x) => {
                    if x != expected[i] {
                        return false;
                    }
                }
                Value::Bool(_) => return false, // int slot got bool
            }
        }
        true
    };

    // Prune by sample signature.
    let signature = |e: &Expr, seen: &mut HashSet<Signature>| -> Option<Signature> {
        let sig: Signature = sample_inputs
            .iter()
            .map(|inp| {
                let env = eval::input_env(spec, inp);
                match eval::eval(e, &env) {
                    Ok(Value::Int(x)) => x,
                    Ok(Value::Bool(b)) => i64::from(b),
                    Err(_) => FAULT_MARKER,
                }
            })
            .collect();
        if seen.insert(sig.clone()) {
            Some(sig)
        } else {
            None
        }
    };

    // Seed: check leaves.
    let mut candidates: Vec<Expr> = Vec::new();
    for e in int_layers[1].clone() {
        stats.candidates_generated += 1;
        if signature(&e, &mut seen_int).is_none() {
            stats.candidates_pruned += 1;
            continue;
        }
        if accepts(&e) {
            return Ok(e);
        }
        candidates.push(e);
    }

    // Grow sizes 2..MAX.
    for size in 2..=MAX_SIZE {
        if stats.candidates_generated > MAX_CANDIDATES {
            break;
        }
        let mut new_int: Vec<Expr> = Vec::new();

        // Unary: neg.
        for e in &candidates {
            stats.candidates_generated += 1;
            let cand = Expr::Unary(UnOp::Neg, Box::new(e.clone()));
            if signature(&cand, &mut seen_int).is_none() {
                stats.candidates_pruned += 1;
                continue;
            }
            if accepts(&cand) {
                return Ok(cand);
            }
            new_int.push(cand);
            if stats.candidates_generated > MAX_CANDIDATES {
                break;
            }
        }

        // Binary int⊗int → int: + - *
        let prev: Vec<Expr> = candidates
            .iter()
            .flat_map(|e| int_layers.iter().flatten().filter(move |x| **x == *e).map(|x| x.clone()))
            .collect();
        let _ = prev;
        // Simpler: all int exprs built so far.
        let all_int: Vec<Expr> = int_layers.iter().flatten().cloned().collect();
        let all_bool: Vec<Expr> = bool_layers.iter().flatten().cloned().collect();

        for a in &all_int {
            for b in &all_int {
                for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
                    stats.candidates_generated += 1;
                    let cand = Expr::Binary(op, Box::new(a.clone()), Box::new(b.clone()));
                    if signature(&cand, &mut seen_int).is_none() {
                        stats.candidates_pruned += 1;
                        continue;
                    }
                    if accepts(&cand) {
                        return Ok(cand);
                    }
                    new_int.push(cand);
                    if stats.candidates_generated > MAX_CANDIDATES {
                        break;
                    }
                }
            }
        }

        // min/max.
        for a in &all_int {
            for b in &all_int {
                for build in [Expr::Min as fn(_, _) -> Expr, Expr::Max] {
                    stats.candidates_generated += 1;
                    let cand = build(Box::new(a.clone()), Box::new(b.clone()));
                    if signature(&cand, &mut seen_int).is_none() {
                        stats.candidates_pruned += 1;
                        continue;
                    }
                    if accepts(&cand) {
                        return Ok(cand);
                    }
                    new_int.push(cand);
                    if stats.candidates_generated > MAX_CANDIDATES {
                        break;
                    }
                }
            }
        }

        // if bool then int else int  (size = 1 + sizes; bound by `size`).
        for c in &all_bool {
            for a in &all_int {
                for b in &all_int {
                    stats.candidates_generated += 1;
                    let cand = Expr::Ite(
                        Box::new(c.clone()),
                        Box::new(a.clone()),
                        Box::new(b.clone()),
                    );
                    if signature(&cand, &mut seen_int).is_none() {
                        stats.candidates_pruned += 1;
                        continue;
                    }
                    if accepts(&cand) {
                        return Ok(cand);
                    }
                    new_int.push(cand);
                    if stats.candidates_generated > MAX_CANDIDATES {
                        break;
                    }
                }
            }
        }

        int_layers[size] = new_int;

        // Grow bool layer: !, &&, ||, comparisons of new int exprs.
        let mut new_bool: Vec<Expr> = Vec::new();
        let all_int_now: Vec<Expr> = int_layers.iter().flatten().cloned().collect();
        let all_bool_now: Vec<Expr> = bool_layers.iter().flatten().cloned().collect();

        for e in &all_bool_now {
            stats.candidates_generated += 1;
            let cand = Expr::Unary(UnOp::Not, Box::new(e.clone()));
            if signature(&cand, &mut seen_bool).is_none() {
                stats.candidates_pruned += 1;
                continue;
            }
            new_bool.push(cand);
        }
        for a in &all_bool_now {
            for b in &all_bool_now {
                for op in [BinOp::And, BinOp::Or] {
                    stats.candidates_generated += 1;
                    let cand = Expr::Binary(op, Box::new(a.clone()), Box::new(b.clone()));
                    if signature(&cand, &mut seen_bool).is_none() {
                        stats.candidates_pruned += 1;
                        continue;
                    }
                    new_bool.push(cand);
                }
            }
        }
        // Comparisons only over *new* ints to bound growth.
        let fresh_ints: Vec<Expr> = int_layers[size].clone();
        for a in &fresh_ints {
            for b in &all_int_now {
                for op in [BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge] {
                    stats.candidates_generated += 1;
                    let cand = Expr::Binary(op, Box::new(a.clone()), Box::new(b.clone()));
                    if signature(&cand, &mut seen_bool).is_none() {
                        stats.candidates_pruned += 1;
                        continue;
                    }
                    new_bool.push(cand);
                }
            }
        }

        bool_layers[size] = new_bool;
    }

    // Nothing in the bounded space matches every example.
    Err(SynthError::Exhausted {
        message: format!(
            "no expression of size ≤ {} over the grammar matches all {} example(s) for result \
             `{}: {}` (generated {}, pruned as observationally equivalent {}) — this is a search \
             bound, not a proof of impossibility; the contract may need a different formulation",
            MAX_SIZE,
            examples.len(),
            result.name,
            result.ty,
            stats.candidates_generated,
            stats.candidates_pruned
        ),
    })
}

fn collect_literals(spec: &Spec) -> Vec<i64> {
    let mut out = vec![0i64, 1, -1];
    fn walk(e: &Expr, out: &mut Vec<i64>) {
        match e {
            Expr::IntLit(v) => {
                if !out.contains(v) {
                    out.push(*v);
                }
            }
            Expr::Unary(_, a) => walk(a, out),
            Expr::Binary(_, l, r) => {
                walk(l, out);
                walk(r, out);
            }
            Expr::Ite(c, a, b) => {
                walk(c, out);
                walk(a, out);
                walk(b, out);
            }
            Expr::Min(a, b) | Expr::Max(a, b) => {
                walk(a, out);
                walk(b, out);
            }
            _ => {}
        }
    }
    for c in spec.requires.iter().chain(spec.ensures.iter()) {
        walk(c, &mut out);
    }
    out.truncate(12); // keep the grammar honest
    out
}

// ---------------------------------------------------------------------------
// Output solving (for CEGIS witness completion)
// ---------------------------------------------------------------------------

/// Find an output tuple satisfying every `ensures` clause at `inputs`.
/// `Ok(None)` ⇒ *no* tuple works ⇒ the spec is unrealizable at this input.
fn solve_outputs(spec: &Spec, inputs: &[i64]) -> Result<Option<Vec<i64>>, SynthError> {
    // Product of result domains, capped.
    let ranges: Vec<i64> = spec
        .results
        .iter()
        .map(|r| match r.ty {
            Type::Int(range) => range.size() as i64,
            Type::Bool => 2,
        })
        .collect();
    let product: u128 = ranges.iter().map(|&r| r as u128).product();
    if product > MAX_REALIZABILITY_PRODUCT {
        return Err(SynthError::Exhausted {
            message: format!(
                "would need to enumerate {} output tuples to complete the CEGIS witness — \
                 above the {} cap; narrow the result domains",
                product, MAX_REALIZABILITY_PRODUCT
            ),
        });
    }

    let mut idx: Vec<i64> = vec![0; spec.results.len()];
    loop {
        let outputs: Vec<i64> = spec
            .results
            .iter()
            .zip(&idx)
            .map(|(r, i)| match r.ty {
                Type::Int(range) => range.lo + i,
                Type::Bool => *i,
            })
            .collect();

        let mut env = eval::input_env(spec, inputs);
        for (r, v) in spec.results.iter().zip(&outputs) {
            env.results.push((r.name.clone(), Value::Int(*v)));
        }
        let all_hold = spec.ensures.iter().all(|c| {
            matches!(eval::eval(c, &env), Ok(Value::Bool(true)))
        });
        if all_hold {
            return Ok(Some(outputs));
        }

        // odometer over result domains
        let mut k = 0;
        loop {
            if k >= idx.len() {
                return Ok(None);
            }
            idx[k] += 1;
            if idx[k] < ranges[k] {
                break;
            }
            idx[k] = 0;
            k += 1;
            if k >= idx.len() {
                return Ok(None);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::sema::analyze;

    #[test]
    fn extracts_transfer_definitions() {
        let s = parse(
            r#"
            spec t(a: int[0..255], b: int[0..255], amount: int[0..255])
              returns (x: int[0..255], y: int[0..255])
              requires amount <= a
              requires b + amount <= 255
              ensures x == a - amount
              ensures y == b + amount
              ensures x + y == a + b
              example (100, 50, 25) => (75, 75)
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        let defs = extract_definitions(&s).unwrap();
        assert_eq!(defs.len(), 2, "both results should be definitional");
        assert_eq!(defs["x"].to_string(), "(a - amount)");
        assert_eq!(defs["y"].to_string(), "(b + amount)");
    }

    #[test]
    fn detects_contradictory_witness() {
        let s = parse(
            r#"
            spec bad(a: int[0..10]) returns (r: int[0..10])
              ensures r == a
              example (3) => (7)
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        let err = validate_examples(&s).unwrap_err();
        assert!(err.to_string().contains("contradicts"), "got: {}", err);
    }

    #[test]
    fn detects_example_outside_requires() {
        let s = parse(
            r#"
            spec bad(a: int[0..10]) returns (r: int[0..10])
              requires a > 5
              ensures r == a
              example (3) => (3)
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        let err = validate_examples(&s).unwrap_err();
        assert!(err.to_string().contains("violate `requires`"), "got: {}", err);
    }

    #[test]
    fn enumerates_identity_when_not_definitional() {
        // ensures uses r in a non-definitional way; example pins it down.
        let s = parse(
            r#"
            spec id(a: int[0..15]) returns (r: int[0..15])
              ensures r >= a
              ensures r <= a
              example (7) => (7)
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        let opts = ProverOptions::default();
        let synth = synthesize(&s, &opts).expect("should synthesize");
        // synthesize() returns Err unless the prover said Proved.
        assert_eq!(synth.body.len(), 1);
    }

    #[test]
    fn synthesizes_max_via_enumeration() {
        let s = parse(
            r#"
            spec max2(a: int[0..63], b: int[0..63]) returns (r: int[0..63])
              ensures r >= a
              ensures r >= b
              ensures r == a || r == b
              example (3, 9) => (9)
              example (9, 3) => (9)
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        let opts = ProverOptions::default();
        let synth = synthesize(&s, &opts).expect("should synthesize max");
        // synthesize() returns Err unless the prover said Proved.
        // The enumerator may find `max(a, b)` or an equivalent ite — both are
        // correct; what matters is that the PROVER certified it. Accept either.
        let v = synth.body[0].value.to_string();
        assert!(
            v.contains("max") || v.contains("if"),
            "expected max or ite, got {}",
            v
        );
    }

    #[test]
    fn synthesizes_min_via_min_builtin() {
        let s = parse(
            r#"
            spec min2(a: int[0..63], b: int[0..63]) returns (r: int[0..63])
              ensures r <= a
              ensures r <= b
              ensures r == a || r == b
              example (3, 9) => (3)
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        let opts = ProverOptions::default();
        let synth = synthesize(&s, &opts).expect("should synthesize min");
        // synthesize() returns Err unless the prover said Proved.
        assert!(
            synth.body[0].value.to_string().contains("min"),
            "expected the min builtin, got {}",
            synth.body[0].value
        );
    }

    #[test]
    fn refuses_unrealizable_spec() {
        // r must equal a+1 AND equal a — impossible at every input.
        let s = parse(
            r#"
            spec impossible(a: int[0..10]) returns (r: int[0..20])
              ensures r == a + 1
              ensures r == a
              example (3) => (4)
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        let opts = ProverOptions::default();
        let err = synthesize(&s, &opts).unwrap_err();
        // The example (3)=>(4) violates ensures #2, caught up front.
        assert!(
            matches!(err, SynthError::SpecInconsistent { .. }),
            "got: {}",
            err
        );
    }

    #[test]
    fn synthesizes_double_via_grammar() {
        let s = parse(
            r#"
            spec dbl(a: int[0..31]) returns (r: int[0..62])
              ensures r >= 2 * a
              ensures r <= 2 * a
              example (5) => (10)
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        let opts = ProverOptions::default();
        let synth = synthesize(&s, &opts).expect("should find 2*a");
        // synthesize() returns Err unless the prover said Proved. The exact
        // shape is the synthesizer's choice (`a + a` is cheaper than `2 * a`
        // and observationally identical) — we only pin down the value here.
        assert_eq!(synth.body.len(), 1);
        assert_eq!(synth.body[0].name, "r");
    }
}
