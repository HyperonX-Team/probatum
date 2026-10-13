//! Semantic analysis: name resolution and type checking.
//!
//! Runs before anything else. A spec that fails this stage can never be
//! proved — the earlier we say so, the cheaper the failure.

use crate::ast::*;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug)]
pub struct SemError {
    pub message: String,
}

impl fmt::Display for SemError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

fn err<T>(message: impl Into<String>) -> Result<T, SemError> {
    Err(SemError {
        message: message.into(),
    })
}

/// Type of an expression under a given environment.
fn check_expr(
    e: &Expr,
    params: &[Binding],
    results: &[Binding],
    assigned: Option<&HashSet<&str>>,
) -> Result<Type, SemError> {
    match e {
        Expr::IntLit(v) => {
            // A bare literal gets the widest range that contains it; actual
            // range enforcement happens at comparison/assignment sites via
            // the evaluator's overflow checks.
            Ok(Type::Int(IntRange::new(*v, *v)))
        }
        Expr::BoolLit(_) => Ok(Type::Bool),
        Expr::Param(name) => {
            // Bare name: resolve to a parameter first, then (in ensures /
            // body contexts) to a result. Shadowing is rejected by `analyze`,
            // so this is unambiguous.
            if let Some(b) = params.iter().find(|b| &b.name == name) {
                return Ok(b.ty);
            }
            if let Some(set) = assigned {
                if !set.contains(name.as_str()) {
                    return err(format!(
                        "`{}` read before it is assigned (in body, results are read-after-write)",
                        name
                    ));
                }
            }
            results
                .iter()
                .find(|b| &b.name == name)
                .map(|b| b.ty)
                .ok_or_else(|| SemError {
                    message: format!("unknown name `{}`", name),
                })
        }
        Expr::Result(name) => {
            if let Some(set) = assigned {
                if !set.contains(name.as_str()) {
                    return err(format!(
                        "`result.{}` read before it is assigned (in body, results are read-after-write)",
                        name
                    ));
                }
            }
            results
                .iter()
                .find(|b| &b.name == name)
                .map(|b| b.ty)
                .ok_or_else(|| SemError {
                    message: format!("unknown result variable `result.{}`", name),
                })
        }
        Expr::Unary(UnOp::Neg, inner) => match check_expr(inner, params, results, assigned)? {
            Type::Int(r) => Ok(Type::Int(IntRange::new(-r.hi, -r.lo))),
            Type::Bool => err("cannot negate a bool with `-` (use `!`)"),
        },
        Expr::Unary(UnOp::Not, inner) => {
            let t = check_expr(inner, params, results, assigned)?;
            if t == Type::Bool {
                Ok(Type::Bool)
            } else {
                err(format!("`!` expects bool, got `{}`", t))
            }
        }
        Expr::Binary(op, l, r) => {
            let lt = check_expr(l, params, results, assigned)?;
            let rt = check_expr(r, params, results, assigned)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => match (lt, rt) {
                    (Type::Int(a), Type::Int(b)) => {
                        let (lo, hi) = match op {
                            BinOp::Add => (a.lo.saturating_add(b.lo), a.hi.saturating_add(b.hi)),
                            BinOp::Sub => (a.lo.saturating_sub(b.hi), a.hi.saturating_sub(b.lo)),
                            BinOp::Mul => {
                                let c = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi];
                                (
                                    c.iter().cloned().min().unwrap(),
                                    c.iter().cloned().max().unwrap(),
                                )
                            }
                            _ => unreachable!(),
                        };
                        Ok(Type::Int(IntRange::new(lo, hi)))
                    }
                    _ => err(format!("`{}` expects int operands, got `{}` and `{}`", op, lt, rt)),
                },
                BinOp::Div | BinOp::Mod => match (lt, rt) {
                    (Type::Int(_), Type::Int(_)) => Ok(lt),
                    _ => err(format!("`{}` expects int operands, got `{}` and `{}`", op, lt, rt)),
                },
                BinOp::Eq | BinOp::Ne => {
                    if compatible(&lt, &rt) {
                        Ok(Type::Bool)
                    } else {
                        err(format!("cannot compare `{}` with `{}`", lt, rt))
                    }
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => match (lt, rt) {
                    (Type::Int(_), Type::Int(_)) => Ok(Type::Bool),
                    _ => err(format!("`{}` expects int operands, got `{}` and `{}`", op, lt, rt)),
                },
                BinOp::And | BinOp::Or => match (lt, rt) {
                    (Type::Bool, Type::Bool) => Ok(Type::Bool),
                    _ => err(format!(
                        "`{}` expects bool operands, got `{}` and `{}`",
                        op, lt, rt
                    )),
                },
            }
        }
        Expr::Ite(c, a, b) => {
            let ct = check_expr(c, params, results, assigned)?;
            if ct != Type::Bool {
                return err(format!("`if` condition must be bool, got `{}`", ct));
            }
            let at = check_expr(a, params, results, assigned)?;
            let bt = check_expr(b, params, results, assigned)?;
            if compatible(&at, &bt) {
                Ok(join(&at, &bt))
            } else {
                err(format!("`if` branches disagree: `{}` vs `{}`", at, bt))
            }
        }
        Expr::Min(a, b) | Expr::Max(a, b) => {
            let at = check_expr(a, params, results, assigned)?;
            let bt = check_expr(b, params, results, assigned)?;
            match (at, bt) {
                (Type::Int(x), Type::Int(y)) => Ok(Type::Int(IntRange::new(
                    x.lo.min(y.lo),
                    x.hi.max(y.hi),
                ))),
                _ => err("`min`/`max` expect int operands"),
            }
        }
    }
}

fn compatible(a: &Type, b: &Type) -> bool {
    matches!((a, b), (Type::Int(_), Type::Int(_))) || (a == b && *a == Type::Bool)
}

/// Public range inference over an environment of parameter ranges.
///
/// Used by the bitblaster to size each node's two's-complement width.
/// Returns `Err` for non-int expressions (bools, unbound names) — the
/// bitblaster treats that as "declines this fragment".
pub fn infer_int(
    e: &Expr,
    env: HashMap<String, IntRange>,
) -> Result<IntRange, String> {
    let bindings: Vec<Binding> = env
        .iter()
        .map(|(name, r)| Binding {
            name: name.clone(),
            ty: Type::Int(*r),
        })
        .collect();
    match check_expr(e, &bindings, &[], None) {
        Ok(Type::Int(r)) => Ok(r),
        Ok(other) => Err(format!("expected int, got `{}`", other)),
        Err(se) => Err(se.message),
    }
}

fn join(a: &Type, b: &Type) -> Type {
    match (a, b) {
        (Type::Int(x), Type::Int(y)) => Type::Int(IntRange::new(x.lo.min(y.lo), x.hi.max(y.hi))),
        _ => Type::Bool,
    }
}

/// Full semantic check of a spec.
pub fn analyze(spec: &Spec) -> Result<(), SemError> {
    // Unique parameter names.
    let mut seen = HashSet::new();
    for p in &spec.params {
        if !seen.insert(p.name.as_str()) {
            return err(format!("duplicate parameter `{}`", p.name));
        }
    }
    let mut rseen = HashSet::new();
    for r in &spec.results {
        if !rseen.insert(r.name.as_str()) {
            return err(format!("duplicate result `{}`", r.name));
        }
    }
    // Result names should not shadow params — otherwise `x` is ambiguous in
    // a way that differs between requires and ensures.
    for r in &spec.results {
        if seen.contains(r.name.as_str()) {
            return err(format!(
                "result `{}` shadows parameter `{}` — rename one; `x` would mean two different things",
                r.name, r.name
            ));
        }
    }

    if spec.params.is_empty() {
        return err("a spec needs at least one parameter");
    }
    if spec.results.is_empty() {
        return err("a spec needs at least one result");
    }

    // requires: over params only.
    for e in &spec.requires {
        let t = check_expr(e, &spec.params, &spec.results, None)?;
        if t != Type::Bool {
            return err(format!("`requires` must be bool, got `{}`: {}", t, e));
        }
    }

    // ensures: over params + results.
    let all: HashSet<&str> = spec.results.iter().map(|r| r.name.as_str()).collect();
    for e in &spec.ensures {
        let t = check_expr(e, &spec.params, &spec.results, Some(&all))?;
        if t != Type::Bool {
            return err(format!("`ensures` must be bool, got `{}`: {}", t, e));
        }
    }

    // Body: single assignment per result (parser enforces shape; here we
    // check types and read-after-write).
    if let Some(body) = &spec.body {
        if body.len() != spec.results.len() {
            return err(format!(
                "body assigns {} time(s) but there are {} result(s)",
                body.len(),
                spec.results.len()
            ));
        }
        let mut assigned: HashSet<&str> = HashSet::new();
        for a in body {
            let decl = spec.results.iter().find(|b| b.name == a.name).ok_or_else(
                || SemError {
                    message: format!("assignment to undeclared result `{}`", a.name),
                },
            )?;
            let t = check_expr(&a.value, &spec.params, &spec.results, Some(&assigned))?;
            // Static range check — deliberately conservative in one direction
            // only. Interval analysis does not reason about `requires`, so it
            // cannot prove that `a - amount >= 0` under `amount <= a`. We
            // therefore reject only *disjoint* ranges (definitely broken, no
            // input can save you) and leave partial-overlap cases to the proof
            // engines, which check every in-domain input (or prove it for all
            // inputs at once) — a rejection here is a static analysis result,
            // a violation there is a theorem.
            if let (Type::Int(expr_r), Type::Int(decl_r)) = (&t, &decl.ty) {
                if expr_r.hi < decl_r.lo || expr_r.lo > decl_r.hi {
                    return err(format!(
                        "assignment to `{}`: expression ranges over {} which is disjoint from \
                         declared `{}` : {} — no input can make this fit",
                        a.name, expr_r, a.name, decl.ty
                    ));
                }
            }
            assigned.insert(&*a.name);
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    #[test]
    fn good_spec_analyzes() {
        let s = parse(
            r#"
            spec f(a: int[0..10]) returns (r: int[0..10])
              requires a > 0
              ensures r == a
            "#,
        )
        .unwrap();
        analyze(&s).unwrap();
    }

    #[test]
    fn rejects_shadowing() {
        let s = parse(
            r#"
            spec f(a: int[0..10], r: int[0..10]) returns (r: int[0..10])
              ensures r == a
            "#,
        )
        .unwrap();
        let e = analyze(&s).unwrap_err();
        assert!(e.message.contains("shadows"), "got: {}", e.message);
    }

    #[test]
    fn rejects_bad_ensures_type() {
        let s = parse(
            r#"
            spec f(a: int[0..10]) returns (r: int[0..10])
              ensures a + r
            "#,
        )
        .unwrap();
        let e = analyze(&s).unwrap_err();
        assert!(e.message.contains("must be bool"), "got: {}", e.message);
    }

    #[test]
    fn rejects_disjoint_body_range() {
        // int[6..10] and int[0..5] are disjoint: no input, precondition or
        // not, can make `a` fit in `r`. Static rejection is correct here.
        let s = parse(
            r#"
            spec f(a: int[6..10]) returns (r: int[0..5])
              ensures r <= 5
            { r := a; }
            "#,
        )
        .unwrap();
        let e = analyze(&s).unwrap_err();
        assert!(e.message.contains("disjoint"), "got: {}", e.message);
    }

    #[test]
    fn overlapping_range_deferred_to_prover() {
        // int[0..10] -> int[0..5] overlaps. Static analysis cannot know
        // whether `requires` saves it, so it must NOT reject here — the
        // proof engines decide, and if no precondition helps, they return a
        // concrete counterexample (e.g. input a=6 ⇒ result 6 out of range).
        let s = parse(
            r#"
            spec f(a: int[0..10]) returns (r: int[0..5])
              requires a <= 5
              ensures r == a
            { r := a; }
            "#,
        )
        .unwrap();
        analyze(&s).expect("overlap + guarding requires must analyze");
    }

    #[test]
    fn rejects_read_before_write_in_body() {
        let s = parse(
            r#"
            spec f(a: int[0..10]) returns (r: int[0..10], q: int[0..10])
              ensures q == r
            { q := result.r; r := a; }
            "#,
        )
        .unwrap();
        // parse succeeds (shape ok); analysis should catch read-before-write
        let e = analyze(&s).unwrap_err();
        assert!(
            e.message.contains("before it is assigned"),
            "got: {}",
            e.message
        );
    }
}
