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
}

impl std::fmt::Display for Fault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Fault::DivByZero => write!(f, "division by zero"),
            Fault::Overflow => write!(f, "arithmetic overflow"),
            Fault::TypeMismatch(what) => write!(f, "type mismatch: {}", what),
        }
    }
}

/// Evaluation environment: parameter values, then result values.
#[derive(Clone, Debug, Default)]
pub struct Env {
    pub params: Vec<(String, Value)>,
    pub results: Vec<(String, Value)>,
}

impl Env {
    pub fn get(&self, name: &str) -> Option<&Value> {
        self.results
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .or_else(|| self.params.iter().rev().find(|(n, _)| n == name))
            .map(|(_, v)| v)
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
    }
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

/// Build the environment for a single input vector (params in declaration order).
pub fn input_env(spec: &Spec, inputs: &[i64]) -> Env {
    debug_assert_eq!(inputs.len(), spec.params.len());
    let params = spec
        .params
        .iter()
        .zip(inputs)
        .map(|(b, v)| (b.name.clone(), Value::Int(*v)))
        .collect();
    Env {
        params,
        results: Vec::new(),
    }
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
        results: Vec::new(),
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
        let v = check_contract(&spec, body, &[100, 50, 25]).unwrap();
        assert!(!v, "should satisfy, not be out-of-domain");
    }

    #[test]
    fn out_of_domain_is_skipped() {
        let spec = transfer();
        let body = spec.body.as_ref().unwrap();
        // amount > a violates requires ⇒ out of domain, not a violation.
        let v = check_contract(&spec, body, &[10, 5, 99]).unwrap();
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
        let res = check_contract(&spec, body, &[8, 0]);
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
        assert!(check_contract(&spec, body, &[8, 0]).unwrap() == false);
    }

    #[test]
    fn examples_pass() {
        let spec = transfer();
        let body = spec.body.as_ref().unwrap();
        let fails = check_examples(&spec, body);
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
        assert!(!check_contract(&spec, body, &[0, 5]).unwrap());
    }
}
