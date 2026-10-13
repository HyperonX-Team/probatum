//! The reference evaluator: the single definition of what intent *means*.
//!
//! Every proof engine (exhaustive, BDD, statistical) and every generated
//! artifact must agree with this file exactly. If they disagree, the
//! certificate is worthless — so this module is deliberately small,
//! boring, and test-covered.
//!
//! Semantics (mathematical integers over i64, guarded by range analysis):
//!
//! * `requires` false ⇒ input is *out of domain* — not a violation, not a
//!   proof obligation. The contract says nothing about it.
//! * `ensures` false ⇒ **violation** (counterexample found).
//! * division/modulo by zero ⇒ **fault**, counted as a violation. A program
//!   that crashes on a valid input has broken its contract.
//! * a result outside its declared range ⇒ **violation**. (For bodies that
//!   pass semantic analysis this is unreachable — but the evaluator checks
//!   anyway: trusting your own analyzer is how bugs become theorems.)
//! * i64 overflow ⇒ **fault**. The type checker computes exact interval
//!   bounds for every node, so a well-typed spec can never reach this; if it
//!   ever does, we report it loudly instead of silently wrapping.

use crate::ast::*;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Int(i64),
    Bool(bool),
}

impl Value {
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(v) => Some(*v),
            Value::Bool(_) => None,
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(v) => write!(f, "{}", v),
            Value::Bool(b) => write!(f, "{}", b),
        }
    }
}

/// A runtime fault — a *crash* on a valid input, which counts as a violation.
#[derive(Clone, Debug, PartialEq)]
pub enum Fault {
    DivByZero,
    Overflow,
    TypeMismatch(&'static str),
    /// `a[i]` with `i` outside the declared index domain. The classic
    /// out-of-bounds bug, made a proof obligation instead of a CVE.
    IndexOutOfRange {
        array: String,
        index: i64,
        lo: i64,
        hi: i64,
    },
    /// An `assert` in the body evaluated to false.
    AssertionFailed { expr: String },
    /// The loop did not finish within the step budget. Reported honestly as a
    /// fault rather than silently accepting a partial execution — a program
    /// that doesn't terminate on a valid input has broken its contract.
    NonTermination { steps: u64 },
    /// A quantifier's bound variable was used outside its scope (internal).
    UnboundVariable,
}

impl std::fmt::Display for Fault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Fault::DivByZero => write!(f, "division by zero"),
            Fault::Overflow => write!(f, "arithmetic overflow"),
            Fault::TypeMismatch(what) => write!(f, "type mismatch: {}", what),
            Fault::IndexOutOfRange {
                array,
                index,
                lo,
                hi,
            } => write!(
                f,
                "index {} out of bounds for `{}` (valid: {}..{})",
                index, array, lo, hi
            ),
            Fault::AssertionFailed { expr } => write!(f, "assertion failed: {}", expr),
            Fault::NonTermination { steps } => write!(
                f,
                "loop did not terminate within {} steps",
                steps
            ),
            Fault::UnboundVariable => write!(f, "unbound variable"),
        }
    }
}

/// Evaluation environment: parameter values, local variables, then results,
/// plus array contents.
///
/// The scalar part stays a flat `Vec` on purpose: the exhaustive engine
/// evaluates millions of times per proof, and a hash lookup per variable
/// would dominate. Arrays are a side table, consulted only by the
/// expressions that actually mention one.
#[derive(Clone, Debug, Default)]
pub struct Env {
    pub params: Vec<(String, Value)>,
    pub locals: Vec<(String, Value)>,
    pub results: Vec<(String, Value)>,
    /// Array name → contents, indexed by (index - declared lo).
    pub arrays: HashMap<String, Vec<i64>>,
}

impl Env {
    pub fn get(&self, name: &str) -> Option<&Value> {
        self.results
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .or_else(|| self.locals.iter().rev().find(|(n, _)| n == name))
            .or_else(|| self.params.iter().rev().find(|(n, _)| n == name))
            .map(|(_, v)| v)
    }

    pub fn set(&mut self, name: &str, v: Value) {
        for slot in [
            &mut self.locals,
            &mut self.results,
            &mut self.params,
        ] {
            if let Some(entry) = slot.iter_mut().rev().find(|(n, _)| n == name) {
                entry.1 = v;
                return;
            }
        }
        self.locals.push((name.to_string(), v));
    }
}

/// Evaluate an expression. Pure; no side effects.
pub fn eval(e: &Expr, env: &Env) -> Result<Value, Fault> {
    match e {
        Expr::IntLit(v) => Ok(Value::Int(*v)),
        Expr::BoolLit(b) => Ok(Value::Bool(*b)),
        Expr::Param(name) | Expr::Result(name) => env
            .get(name)
            .cloned()
            .ok_or(Fault::TypeMismatch("unbound variable")),
        Expr::Unary(UnOp::Neg, inner) => match eval(inner, env)? {
            Value::Int(v) => v.checked_neg().map(Value::Int).ok_or(Fault::Overflow),
            Value::Bool(_) => Err(Fault::TypeMismatch("neg of bool")),
        },
        Expr::Unary(UnOp::Not, inner) => match eval(inner, env)? {
            Value::Bool(b) => Ok(Value::Bool(!b)),
            Value::Int(_) => Err(Fault::TypeMismatch("not of int")),
        },
        Expr::Binary(op, l, r) => eval_binary(*op, l, r, env),
        Expr::Ite(c, a, b) => match eval(c, env)? {
            // Lazy: the untaken branch is never evaluated, so
            // `if b != 0 then a/b else 0` is safe by construction.
            Value::Bool(true) => eval(a, env),
            Value::Bool(false) => eval(b, env),
            Value::Int(_) => Err(Fault::TypeMismatch("if condition not bool")),
        },
        Expr::Min(a, b) => {
            let x = eval(a, env)?.as_int().ok_or(Fault::TypeMismatch("min"))?;
            let y = eval(b, env)?.as_int().ok_or(Fault::TypeMismatch("min"))?;
            Ok(Value::Int(x.min(y)))
        }
        Expr::Max(a, b) => {
            let x = eval(a, env)?.as_int().ok_or(Fault::TypeMismatch("max"))?;
            let y = eval(b, env)?.as_int().ok_or(Fault::TypeMismatch("max"))?;
            Ok(Value::Int(x.max(y)))
        }
        // ---- arrays -------------------------------------------------------
        Expr::ArrayRead(name, index) => {
            let i = eval(index, env)?
                .as_int()
                .ok_or(Fault::TypeMismatch("array index"))?;
            let contents = env
                .arrays
                .get(name)
                .ok_or(Fault::TypeMismatch("array not initialised"))?;
            // Contents are stored in index order starting at the declared lo;
            // an out-of-range index is a fault, never a silent default.
            let len = contents.len() as i64;
            if i < 0 || i >= len {
                return Err(Fault::IndexOutOfRange {
                    array: name.clone(),
                    index: i,
                    lo: 0,
                    hi: len - 1,
                });
            }
            Ok(Value::Int(contents[i as usize]))
        }
        Expr::Len(name) => {
            let contents = env
                .arrays
                .get(name)
                .ok_or(Fault::TypeMismatch("array not initialised"))?;
            Ok(Value::Int(contents.len() as i64))
        }

        // ---- quantifiers and folds ----------------------------------------
        Expr::Forall { var, lo, hi, body } => {
            let (l, h) = eval_bounds(lo, hi, env)?;
            for i in l..=h {
                let mut inner = env.clone();
                inner.locals.push((var.clone(), Value::Int(i)));
                if eval(body, &inner)? != Value::Bool(true) {
                    return Ok(Value::Bool(false));
                }
            }
            Ok(Value::Bool(true))
        }
        Expr::Exists { var, lo, hi, body } => {
            let (l, h) = eval_bounds(lo, hi, env)?;
            for i in l..=h {
                let mut inner = env.clone();
                inner.locals.push((var.clone(), Value::Int(i)));
                if eval(body, &inner)? == Value::Bool(true) {
                    return Ok(Value::Bool(true));
                }
            }
            Ok(Value::Bool(false))
        }
        Expr::Sum { var, lo, hi, body } => {
            let (l, h) = eval_bounds(lo, hi, env)?;
            let mut acc: i64 = 0;
            for i in l..=h {
                let mut inner = env.clone();
                inner.locals.push((var.clone(), Value::Int(i)));
                let v = eval(body, &inner)?
                    .as_int()
                    .ok_or(Fault::TypeMismatch("sum body"))?;
                acc = acc.checked_add(v).ok_or(Fault::Overflow)?;
            }
            Ok(Value::Int(acc))
        }
    }
}

/// Evaluate a quantifier's bounds (both must be concrete integers).
fn eval_bounds(lo: &Expr, hi: &Expr, env: &Env) -> Result<(i64, i64), Fault> {
    let l = eval(lo, env)?
        .as_int()
        .ok_or(Fault::TypeMismatch("quantifier bound"))?;
    let h = eval(hi, env)?
        .as_int()
        .ok_or(Fault::TypeMismatch("quantifier bound"))?;
    Ok((l, h))
}

fn eval_binary(op: BinOp, l: &Expr, r: &Expr, env: &Env) -> Result<Value, Fault> {
    // Short-circuit logical operators: don't evaluate RHS when LHS decides.
    match op {
        BinOp::And => {
            return match eval(l, env)? {
                Value::Bool(false) => Ok(Value::Bool(false)),
                Value::Bool(true) => match eval(r, env)? {
                    Value::Bool(b) => Ok(Value::Bool(b)),
                    Value::Int(_) => Err(Fault::TypeMismatch("and rhs not bool")),
                },
                Value::Int(_) => Err(Fault::TypeMismatch("and lhs not bool")),
            }
        }
        BinOp::Or => {
            return match eval(l, env)? {
                Value::Bool(true) => Ok(Value::Bool(true)),
                Value::Bool(false) => match eval(r, env)? {
                    Value::Bool(b) => Ok(Value::Bool(b)),
                    Value::Int(_) => Err(Fault::TypeMismatch("or rhs not bool")),
                },
                Value::Int(_) => Err(Fault::TypeMismatch("or lhs not bool")),
            }
        }
        _ => {}
    }

    let lv = eval(l, env)?;
    let rv = eval(r, env)?;

    // Comparisons.
    match op {
        BinOp::Eq => {
            return Ok(Value::Bool(lv == rv));
        }
        BinOp::Ne => {
            return Ok(Value::Bool(lv != rv));
        }
        _ => {}
    }

    let (a, b) = match (lv, rv) {
        (Value::Int(a), Value::Int(b)) => (a, b),
        _ => return Err(Fault::TypeMismatch("int operand expected")),
    };

    match op {
        BinOp::Add => a.checked_add(b).map(Value::Int).ok_or(Fault::Overflow),
        BinOp::Sub => a.checked_sub(b).map(Value::Int).ok_or(Fault::Overflow),
        BinOp::Mul => a.checked_mul(b).map(Value::Int).ok_or(Fault::Overflow),
        BinOp::Div => {
            if b == 0 {
                Err(Fault::DivByZero)
            } else {
                // Truncate toward zero — matches Rust and Go codegen exactly.
                a.checked_div(b).map(Value::Int).ok_or(Fault::Overflow)
            }
        }
        BinOp::Mod => {
            if b == 0 {
                Err(Fault::DivByZero)
            } else {
                a.checked_rem(b).map(Value::Int).ok_or(Fault::Overflow)
            }
        }
        BinOp::Lt => Ok(Value::Bool(a < b)),
        BinOp::Le => Ok(Value::Bool(a <= b)),
        BinOp::Gt => Ok(Value::Bool(a > b)),
        BinOp::Ge => Ok(Value::Bool(a >= b)),
        BinOp::Eq => Ok(Value::Bool(a == b)),
        BinOp::Ne => Ok(Value::Bool(a != b)),
        BinOp::And | BinOp::Or => unreachable!("handled above"),
    }
}

/// Why a particular input failed the contract.
#[derive(Clone, Debug, PartialEq)]
pub enum Violation {
    /// `ensures` clause #i evaluated to false.
    EnsuresFalse { clause: usize, expr: Expr },
    /// Evaluation faulted (div-by-zero / overflow / type error).
    Faulted { fault: Fault },
    /// A result landed outside its declared domain.
    OutOfRange { result: String, value: i64, range: IntRange },
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Violation::EnsuresFalse { clause, expr } => {
                write!(f, "ensures #{} false: {}", clause + 1, expr)
            }
            Violation::Faulted { fault } => write!(f, "fault: {}", fault),
            Violation::OutOfRange {
                result,
                value,
                range,
            } => write!(
                f,
                "result `{}` = {} outside declared {}",
                result, value, range
            ),
        }
    }
}

/// Build the environment for a single input vector.
///
/// Array parameters consume consecutive slots (one per element), so a spec
/// with `a: int[0..3]` as an array plus `n: int[0..9]` takes 5 slots.
pub fn input_env(spec: &Spec, inputs: &[i64]) -> Env {
    let mut env = Env::default();
    // Ignore a binding failure here: callers that care use `Machine::new`,
    // which reports the fault. `input_env` is the lenient path used when
    // evaluating preconditions on data the domain already covers.
    let _ = bind_params(spec, inputs, &mut env);
    env
}

/// Do the inputs satisfy `requires`? (Out-of-domain inputs are skipped.)
pub fn precondition_holds(spec: &Spec, inputs: &[i64]) -> bool {
    let env = input_env(spec, inputs);
    spec.requires.iter().all(|e| {
        eval(e, &env)
            .map(|v| v == Value::Bool(true))
            .unwrap_or(false) // a faulting precondition means the input is unusable
    })
}

/// Run a body (program) on inputs. Returns result values in declaration order.
pub fn run_body(spec: &Spec, body: &[Assign], inputs: &[i64]) -> Result<Vec<Value>, Fault> {
    let mut env = input_env(spec, inputs);
    for a in body {
        let v = eval(&a.value, &env)?;
        env.results.push((a.name.clone(), v));
    }
    // Return in *declaration* order, not assignment order.
    Ok(spec
        .results
        .iter()
        .map(|b| {
            env.results
                .iter()
                .find(|(n, _)| n == &b.name)
                .map(|(_, v)| v.clone())
                .expect("body must assign every result (parser-enforced)")
        })
        .collect())
}

/// Check the full contract on one input vector.
///
/// * `Ok(true)`  — input out of domain (precondition false): nothing to prove.
/// * `Ok(false)` — contract satisfied.
/// * `Err(v)`    — **violation**: here is the counterexample's cause.
pub fn check_contract(
    spec: &Spec,
    body: &[Assign],
    inputs: &[i64],
) -> Result<bool, Violation> {
    if !precondition_holds(spec, inputs) {
        return Ok(true); // out of domain — vacuously fine
    }

    let outputs = match run_body(spec, body, inputs) {
        Ok(o) => o,
        Err(fault) => return Err(Violation::Faulted { fault }),
    };

    // Defense in depth: results must respect declared domains.
    for (b, v) in spec.results.iter().zip(&outputs) {
        if let (Type::Int(r), Value::Int(val)) = (&b.ty, v) {
            if !r.contains(*val) {
                return Err(Violation::OutOfRange {
                    result: b.name.clone(),
                    value: *val,
                    range: *r,
                });
            }
        }
    }

    let mut env = input_env(spec, inputs);
    for (b, v) in spec.results.iter().zip(&outputs) {
        env.results.push((b.name.clone(), v.clone()));
    }

    for (i, clause) in spec.ensures.iter().enumerate() {
        match eval(clause, &env) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(Violation::EnsuresFalse {
                    clause: i,
                    expr: clause.clone(),
                })
            }
            Ok(Value::Int(_)) => {
                return Err(Violation::Faulted {
                    fault: Fault::TypeMismatch("ensures not bool"),
                })
            }
            Err(fault) => return Err(Violation::Faulted { fault }),
        }
    }

    Ok(false) // in domain, all clauses held
}

// ---------------------------------------------------------------------------
// The program machine: statements, control flow, arrays
// ---------------------------------------------------------------------------

/// How many statement-steps a single execution may take before we declare
/// non-termination. High enough for any loop over a bounded domain, low
/// enough to fail fast on a runaway.
pub const DEFAULT_STEP_LIMIT: u64 = 2_000_000;

/// Number of scalar input slots a spec consumes. An array parameter takes one
/// slot per element, in index order.
pub fn input_arity(spec: &Spec) -> usize {
    spec.params
        .iter()
        .map(|b| match b.ty {
            Type::Array { index, .. } => index.size() as usize,
            _ => 1,
        })
        .sum()
}

/// Bind an input vector into an environment: scalars to `params`, array
/// parameters to `arrays`. Array elements are range-checked here.
fn bind_params(spec: &Spec, inputs: &[i64], env: &mut Env) -> Result<(), Fault> {
    let mut k = 0usize;
    for b in &spec.params {
        match b.ty {
            Type::Array { index, elem } => {
                let n = index.size() as usize;
                let mut vals = Vec::with_capacity(n);
                for _ in 0..n {
                    let v = *inputs
                        .get(k)
                        .ok_or(Fault::TypeMismatch("too few inputs for array parameter"))?;
                    if !elem.contains(v) {
                        return Err(Fault::IndexOutOfRange {
                            array: b.name.clone(),
                            index: v,
                            lo: elem.lo,
                            hi: elem.hi,
                        });
                    }
                    vals.push(v);
                    k += 1;
                }
                env.arrays.insert(b.name.clone(), vals);
            }
            _ => {
                let v = *inputs
                    .get(k)
                    .ok_or(Fault::TypeMismatch("too few inputs"))?;
                env.params.push((b.name.clone(), Value::Int(v)));
                k += 1;
            }
        }
    }
    Ok(())
}

/// The execution machine: environment plus a step budget.
pub struct Machine<'a> {
    pub spec: &'a Spec,
    pub env: Env,
    pub steps: u64,
    pub max_steps: u64,
}

impl<'a> Machine<'a> {
    pub fn new(spec: &'a Spec, inputs: &[i64]) -> Result<Self, Fault> {
        let mut env = Env::default();
        bind_params(spec, inputs, &mut env)?;
        // Locals start at the bottom of their declared domain. Arrays too:
        // explicit, documented, and the invariant in the loop says what the
        // values mean from then on.
        for l in &spec.locals {
            match l.ty {
                Type::Array { index, elem } => {
                    let n = index.size() as usize;
                    env.arrays.insert(l.name.clone(), vec![elem.lo; n]);
                }
                _ => {
                    let lo = l.ty.as_int_range().map(|r| r.lo).unwrap_or(0);
                    env.locals.push((l.name.clone(), Value::Int(lo)));
                }
            }
        }
        Ok(Machine {
            spec,
            env,
            steps: 0,
            max_steps: DEFAULT_STEP_LIMIT,
        })
    }

    fn tick(&mut self) -> Result<(), Fault> {
        self.steps += 1;
        if self.steps > self.max_steps {
            return Err(Fault::NonTermination { steps: self.max_steps });
        }
        Ok(())
    }

    pub fn exec_block(&mut self, prog: &[Stmt]) -> Result<(), Fault> {
        for s in prog {
            self.exec_stmt(s)?;
        }
        Ok(())
    }

    pub fn exec_stmt(&mut self, s: &Stmt) -> Result<(), Fault> {
        self.tick()?;
        match s {
            Stmt::Assign { name, value } => {
                let v = eval(value, &self.env)?;
                self.env.set(name, v);
            }
            Stmt::ArrayAssign {
                array,
                index,
                value,
            } => {
                let i = eval(index, &self.env)?
                    .as_int()
                    .ok_or(Fault::TypeMismatch("array index"))?;
                let v = eval(value, &self.env)?
                    .as_int()
                    .ok_or(Fault::TypeMismatch("array element"))?;
                let contents = self
                    .env
                    .arrays
                    .get_mut(array)
                    .ok_or(Fault::TypeMismatch("array not initialised"))?;
                let len = contents.len() as i64;
                if i < 0 || i >= len {
                    return Err(Fault::IndexOutOfRange {
                        array: array.clone(),
                        index: i,
                        lo: 0,
                        hi: len - 1,
                    });
                }
                contents[i as usize] = v;
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                if eval(cond, &self.env)? == Value::Bool(true) {
                    self.exec_block(then_body)?;
                } else {
                    self.exec_block(else_body)?;
                }
            }
            Stmt::While { cond, body, .. } => loop {
                self.tick()?;
                match eval(cond, &self.env)? {
                    Value::Bool(true) => self.exec_block(body)?,
                    Value::Bool(false) => break,
                    Value::Int(_) => return Err(Fault::TypeMismatch("while condition not bool")),
                }
            },
            Stmt::Assert(e) => {
                if eval(e, &self.env)? != Value::Bool(true) {
                    return Err(Fault::AssertionFailed {
                        expr: e.to_string(),
                    });
                }
            }
        }
        Ok(())
    }

    /// Result values in declaration order.
    pub fn results(&self) -> Vec<Value> {
        self.spec
            .results
            .iter()
            .map(|b| match b.ty {
                Type::Array { .. } => {
                    // Array results are returned element-wise.
                    Value::Int(
                        self.env
                            .arrays
                            .get(&b.name)
                            .map(|v| v.len() as i64)
                            .unwrap_or(0),
                    )
                }
                _ => self
                    .env
                    .get(&b.name)
                    .cloned()
                    .unwrap_or(Value::Int(0)),
            })
            .collect()
    }

    /// Array result contents (element order), for contract clauses that
    /// mention `result[i]`.
    pub fn arrays(&self) -> &HashMap<String, Vec<i64>> {
        &self.env.arrays
    }
}

/// Execute a full program (statements, loops, arrays) on one input vector.
pub fn run_program(spec: &Spec, prog: &Program, inputs: &[i64]) -> Result<Vec<Value>, Fault> {
    let mut m = Machine::new(spec, inputs)?;
    m.exec_block(prog)?;
    Ok(m.results())
}

/// Check the full contract for a *program* (with control flow) on one input.
///
/// Same contract semantics as `check_contract`, but the body is a statement
/// program executed by the machine. Returns `Ok(true)` for out-of-domain
/// inputs, `Ok(false)` when satisfied, `Err` for a violation.
pub fn check_contract_program(
    spec: &Spec,
    prog: &Program,
    inputs: &[i64],
) -> Result<bool, Violation> {
    if !precondition_holds(spec, inputs) {
        return Ok(true);
    }
    let mut m = match Machine::new(spec, inputs) {
        Ok(m) => m,
        Err(f) => return Err(Violation::Faulted { fault: f }),
    };
    if let Err(f) = m.exec_block(prog) {
        return Err(Violation::Faulted { fault: f });
    }
    let outputs = m.results();
    for (b, v) in spec.results.iter().zip(&outputs) {
        if let (Type::Int(r), Value::Int(val)) = (&b.ty, v) {
            if !r.contains(*val) {
                return Err(Violation::OutOfRange {
                    result: b.name.clone(),
                    value: *val,
                    range: *r,
                });
            }
        }
    }
    // Bind outputs (and any result arrays) for the ensures clauses.
    let mut env = input_env(spec, inputs);
    for (b, v) in spec.results.iter().zip(&outputs) {
        env.results.push((b.name.clone(), v.clone()));
    }
    for (name, contents) in m.arrays() {
        if spec.results.iter().any(|r| &r.name == name) {
            env.arrays.insert(name.clone(), contents.clone());
        }
    }
    for (i, clause) in spec.ensures.iter().enumerate() {
        match eval(clause, &env) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(Violation::EnsuresFalse {
                    clause: i,
                    expr: clause.clone(),
                })
            }
            Ok(Value::Int(_)) => {
                return Err(Violation::Faulted {
                    fault: Fault::TypeMismatch("ensures not bool"),
                })
            }
            Err(fault) => return Err(Violation::Faulted { fault }),
        }
    }
    Ok(false)
}

/// Check the examples for a statement program (control flow included).
pub fn check_examples_program(
    spec: &Spec,
    prog: &Program,
) -> Vec<(usize, Vec<i64>, Result<Vec<Value>, Fault>, Vec<i64>)> {
    spec.examples
        .iter()
        .enumerate()
        .filter_map(|(i, ex)| {
            let got = run_program(spec, prog, &ex.inputs);
            match &got {
                Ok(vals)
                    if *vals
                        == ex
                            .outputs
                            .iter()
                            .map(|v| Value::Int(*v))
                            .collect::<Vec<_>>() =>
                {
                    None
                }
                _ => Some((i, ex.inputs.clone(), got, ex.outputs.clone())),
            }
        })
        .collect()
}

/// Check the examples: run the body on each witness and compare outputs.
pub fn check_examples(
    spec: &Spec,
    body: &[Assign],
) -> Vec<(usize, Vec<i64>, Result<Vec<Value>, Fault>, Vec<i64>)> {
    spec.examples
        .iter()
        .enumerate()
        .filter_map(|(i, ex)| {
            // Examples whose inputs are out of domain were already rejected
            // by the parser; here we only care about execution.
            let got = run_body(spec, body, &ex.inputs);
            match &got {
                Ok(vals) if *vals
                    == ex
                        .outputs
                        .iter()
                        .map(|v| Value::Int(*v))
                        .collect::<Vec<_>>() =>
                {
                    None // pass
                }
                _ => Some((i, ex.inputs.clone(), got, ex.outputs.clone())),
            }
        })
        .collect()
}

#[allow(dead_code)]
pub fn env_from(spec: &Spec, inputs: &HashMap<String, i64>) -> Env {
    let params = spec
        .params
        .iter()
        .map(|b| {
            let v = inputs.get(&b.name).copied().unwrap_or(0);
            (b.name.clone(), Value::Int(v))
        })
        .collect();
    Env {
        params,
        locals: Vec::new(),
        results: Vec::new(),
        arrays: HashMap::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::sema::analyze;

    fn transfer() -> Spec {
        let s = parse(
            r#"
            spec transfer(a: int[0..255], b: int[0..255], amount: int[0..255])
              returns (x: int[0..255], y: int[0..255])
              requires amount <= a
              requires b + amount <= 255
              ensures x == a - amount
              ensures y == b + amount
              ensures x + y == a + b
              example (100, 50, 25) => (75, 75)
            {
              x := a - amount;
              y := b + amount;
            }
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
        s
    }

    #[test]
    fn valid_input_satisfies_contract() {
        let spec = transfer();
        let body = spec.body.as_ref().unwrap();
        let v = check_contract_program(&spec, body, &[100, 50, 25]).unwrap();
        assert!(!v, "should satisfy, not be out-of-domain");
    }

    #[test]
    fn out_of_domain_is_skipped() {
        let spec = transfer();
        let body = spec.body.as_ref().unwrap();
        // amount > a violates requires ⇒ out of domain, not a violation.
        let v = check_contract_program(&spec, body, &[10, 5, 99]).unwrap();
        assert!(v, "should be out of domain");
    }

    #[test]
    fn div_by_zero_is_a_violation() {
        let spec = parse(
            r#"
            spec d(a: int[0..10], b: int[0..10])
              returns (r: int[0..10])
              ensures r == a / b
            { r := a / b; }
            "#,
        )
        .unwrap();
        analyze(&spec).unwrap();
        let body = spec.body.as_ref().unwrap();
        let res = check_contract_program(&spec, body, &[8, 0]);
        assert!(
            matches!(res, Err(Violation::Faulted { fault: Fault::DivByZero })),
            "got {:?}",
            res
        );
    }

    #[test]
    fn lazy_ite_avoids_div_fault() {
        let spec = parse(
            r#"
            spec d(a: int[0..10], b: int[0..10])
              returns (r: int[0..10])
              requires true
              ensures r == if b == 0 then 0 else a / b
            { r := if b == 0 then 0 else a / b; }
            "#,
        )
        .unwrap();
        analyze(&spec).unwrap();
        let body = spec.body.as_ref().unwrap();
        assert!(check_contract_program(&spec, body, &[8, 0]).unwrap() == false);
    }

    #[test]
    fn examples_pass() {
        let spec = transfer();
        let body = spec.body.as_ref().unwrap();
        let fails = check_examples_program(&spec, body);
        assert!(fails.is_empty(), "unexpected example failures: {:?}", fails);
    }

    #[test]
    fn short_circuit_and_skips_rhs() {
        // RHS would fault if evaluated.
        let spec = parse(
            r#"
            spec s(a: int[0..10], b: int[0..10])
              returns (r: bool)
              ensures r == (a == 0 || b / a > 1)
            { r := a == 0 || b / a > 1; }
            "#,
        )
        .unwrap();
        analyze(&spec).unwrap();
        let body = spec.body.as_ref().unwrap();
        // a == 0 ⇒ short-circuit, no fault.
        assert!(!check_contract_program(&spec, body, &[0, 5]).unwrap());
    }
}
