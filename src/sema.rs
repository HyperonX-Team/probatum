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
///
/// Scope resolution order: parameters, then locals, then results. Shadowing
/// is rejected by `analyze`, so a bare name is never ambiguous.
fn check_expr(
    e: &Expr,
    params: &[Binding],
    locals: &[Binding],
    results: &[Binding],
    assigned: Option<&HashSet<String>>,
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
            // Bare name: parameters first, then locals, then (in ensures /
            // body contexts) results.
            if let Some(b) = params.iter().find(|b| &b.name == name) {
                return Ok(b.ty);
            }
            if let Some(b) = locals.iter().find(|b| &b.name == name) {
                return Ok(b.ty);
            }
            if let Some(set) = assigned {
                if !set.contains(name.as_str()) {
                    return err(format!(
                        "`{}` read before it is assigned (definite-assignment check)",
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
                        "`result.{}` read before it is assigned",
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
        Expr::Unary(UnOp::Neg, inner) => {
            match check_expr(inner, params, locals, results, assigned)? {
                Type::Int(r) => Ok(Type::Int(IntRange::new(-r.hi, -r.lo))),
                Type::Bool => err("cannot negate a bool with `-` (use `!`)"),
                other => err(format!("cannot negate `{}`", other)),
            }
        }
        Expr::Unary(UnOp::Not, inner) => {
            let t = check_expr(inner, params, locals, results, assigned)?;
            if t == Type::Bool {
                Ok(Type::Bool)
            } else {
                err(format!("`!` expects bool, got `{}`", t))
            }
        }
        Expr::Binary(op, l, r) => {
            let lt = check_expr(l, params, locals, results, assigned)?;
            let rt = check_expr(r, params, locals, results, assigned)?;
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
            let ct = check_expr(c, params, locals, results, assigned)?;
            if ct != Type::Bool {
                return err(format!("`if` condition must be bool, got `{}`", ct));
            }
            let at = check_expr(a, params, locals, results, assigned)?;
            let bt = check_expr(b, params, locals, results, assigned)?;
            if compatible(&at, &bt) {
                Ok(join(&at, &bt))
            } else {
                err(format!("`if` branches disagree: `{}` vs `{}`", at, bt))
            }
        }
        Expr::Min(a, b) | Expr::Max(a, b) => {
            let at = check_expr(a, params, locals, results, assigned)?;
            let bt = check_expr(b, params, locals, results, assigned)?;
            match (at, bt) {
                (Type::Int(x), Type::Int(y)) => Ok(Type::Int(IntRange::new(
                    x.lo.min(y.lo),
                    x.hi.max(y.hi),
                ))),
                _ => err("`min`/`max` expect int operands"),
            }
        }
        // ---- quantifiers and folds ----------------------------------------
        Expr::Forall { var, lo, hi, body } | Expr::Exists { var, lo, hi, body } => {
            let bound = check_bound_range(lo, hi, var, params, locals, results, assigned)?;
            // Inside the quantifier the bound variable is a fresh integer in
            // [lo, hi]; shadowing an existing name is rejected.
            let mut inner_locals = locals.to_vec();
            if inner_locals.iter().any(|b| &b.name == var)
                || params.iter().any(|b| &b.name == var)
            {
                return err(format!(
                    "quantifier variable `{}` shadows an existing variable",
                    var
                ));
            }
            inner_locals.push(Binding {
                name: var.clone(),
                ty: Type::Int(bound),
            });
            let bt = check_expr(body, params, &inner_locals, results, assigned)?;
            if bt != Type::Bool {
                return err(format!(
                    "quantifier body must be bool, got `{}`: {}",
                    bt, body
                ));
            }
            Ok(Type::Bool)
        }
        Expr::Sum { var, lo, hi, body } => {
            let bound = check_bound_range(lo, hi, var, params, locals, results, assigned)?;
            let mut inner_locals = locals.to_vec();
            if inner_locals.iter().any(|b| &b.name == var)
                || params.iter().any(|b| &b.name == var)
            {
                return err(format!(
                    "quantifier variable `{}` shadows an existing variable",
                    var
                ));
            }
            inner_locals.push(Binding {
                name: var.clone(),
                ty: Type::Int(bound),
            });
            let bt = check_expr(body, params, &inner_locals, results, assigned)?;
            match bt {
                Type::Int(elem) => {
                    // Worst-case magnitude: n * max|elem|, computed in i128 to
                    // avoid overflow while bounding the sum.
                    let n = bound.size() as i128;
                    let mag = elem
                        .lo
                        .unsigned_abs()
                        .max(elem.hi.unsigned_abs()) as i128;
                    let total = n * mag;
                    if total > i64::MAX as i128 {
                        return err(format!(
                            "`sum` over {} iterations of values up to {} can exceed i64 — \
                             narrow the domain or the element range",
                            n, mag
                        ));
                    }
                    Ok(Type::Int(IntRange::new(
                        -(total as i64),
                        total as i64,
                    )))
                }
                other => err(format!("`sum` body must be int, got `{}`", other)),
            }
        }
        // ---- arrays --------------------------------------------------------
        Expr::ArrayRead(name, index) => {
            let elem = lookup_array(name, params, locals, results)?;
            let it = check_expr(index, params, locals, results, assigned)?;
            match it {
                Type::Int(_) => Ok(Type::Int(elem)),
                other => err(format!("array index must be int, got `{}`", other)),
            }
        }
        Expr::Len(name) => {
            let _ = lookup_array(name, params, locals, results)?;
            // Length is a compile-time constant; report its exact range.
            let r = array_index_range(name, params, locals, results)?;
            Ok(Type::Int(IntRange::new(r.size() as i64, r.size() as i64)))
        }
    }
}

/// Check the bounds of a quantifier and return the bound variable's domain.
///
/// Bounds may be **symbolic** — `sum(k in 0..i-1: k)` inside a loop invariant
/// is the whole point. The bound variable's domain is therefore the widest
/// span the bounds can take, which keeps every downstream range computation a
/// sound over-approximation: it can reject a valid program, never accept an
/// invalid one.
fn check_bound_range(
    lo: &Expr,
    hi: &Expr,
    var: &str,
    params: &[Binding],
    locals: &[Binding],
    results: &[Binding],
    assigned: Option<&HashSet<String>>,
) -> Result<IntRange, SemError> {
    let _ = var;
    match (
        check_expr(lo, params, locals, results, assigned)?,
        check_expr(hi, params, locals, results, assigned)?,
    ) {
        (Type::Int(l), Type::Int(h)) => {
            if l.lo > h.hi {
                // Provably empty for every input. An empty fold is 0 and an
                // empty `forall` is true, so this is legal — just never runs.
                return Ok(IntRange::new(l.lo, l.lo));
            }
            Ok(IntRange::new(l.lo, h.hi))
        }
        _ => err(format!("quantifier bounds for `{}` must be int", var)),
    }
}

/// The element type of a declared array, or an error naming the offender.
pub fn lookup_array(
    name: &str,
    params: &[Binding],
    locals: &[Binding],
    results: &[Binding],
) -> Result<IntRange, SemError> {
    for b in params.iter().chain(locals.iter()).chain(results.iter()) {
        if b.name == name {
            return match b.ty {
                Type::Array { elem, .. } => Ok(elem),
                other => err(format!("`{}` is `{}`, not an array", name, other)),
            };
        }
    }
    err(format!("unknown array `{}`", name))
}

/// The index domain of a declared array.
pub fn array_index_range(
    name: &str,
    params: &[Binding],
    locals: &[Binding],
    results: &[Binding],
) -> Result<IntRange, SemError> {
    for b in params.iter().chain(locals.iter()).chain(results.iter()) {
        if b.name == name {
            return match b.ty {
                Type::Array { index, .. } => Ok(index),
                other => err(format!("`{}` is `{}`, not an array", name, other)),
            };
        }
    }
    err(format!("unknown array `{}`", name))
}

fn compatible(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Int(_), Type::Int(_)) => true,
        (Type::Decimal { scale: s1, .. }, Type::Decimal { scale: s2, .. }) => s1 == s2,
        (Type::Bool, Type::Bool) => true,
        (
            Type::Array {
                index: i1,
                elem: e1,
            },
            Type::Array {
                index: i2,
                elem: e2,
            },
        ) => i1 == i2 && e1 == e2,
        _ => false,
    }
}

/// Public range inference over an environment of parameter ranges.
///
/// Used by the bitblaster to size each node's two's-complement width.
/// Returns `Err` for non-int expressions (bools, unbound names) — the
/// bitblaster treats that as "declines this fragment".
pub fn infer_int(e: &Expr, env: HashMap<String, IntRange>) -> Result<IntRange, String> {
    let bindings: Vec<Binding> = env
        .iter()
        .map(|(name, r)| Binding {
            name: name.clone(),
            ty: Type::Int(*r),
        })
        .collect();
    match check_expr(e, &bindings, &[], &[], None) {
        Ok(Type::Int(r)) => Ok(r),
        Ok(other) => Err(format!("expected int, got `{}`", other)),
        Err(se) => Err(se.message),
    }
}

fn join(a: &Type, b: &Type) -> Type {
    match (a, b) {
        (Type::Int(x), Type::Int(y)) => Type::Int(IntRange::new(x.lo.min(y.lo), x.hi.max(y.hi))),
        (Type::Decimal { scale, stored: x }, Type::Decimal { stored: y, .. }) => Type::Decimal {
            scale: *scale,
            stored: IntRange::new(x.lo.min(y.lo), x.hi.max(y.hi)),
        },
        _ => Type::Bool,
    }
}

// ---------------------------------------------------------------------------
// Statement checking
// ---------------------------------------------------------------------------

fn check_program(spec: &Spec, prog: &[Stmt]) -> Result<(), SemError> {
    let mut definite: HashSet<String> = HashSet::new();
    check_stmts(spec, prog, &mut definite, 0)?;

    // Every declared result must be assigned somewhere, or the contract is
    // about a value that never exists.
    let mut assigned_all: Vec<String> = Vec::new();
    collect_assigned(prog, &mut assigned_all);
    for r in &spec.results {
        if !assigned_all.iter().any(|n| n == &r.name) {
            return err(format!("result `{}` is never assigned in the body", r.name));
        }
    }
    Ok(())
}

fn collect_assigned(prog: &[Stmt], out: &mut Vec<String>) {
    for s in prog {
        match s {
            Stmt::Assign { name, .. } => out.push(name.clone()),
            Stmt::ArrayAssign { array, .. } => out.push(array.clone()),
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_assigned(then_body, out);
                collect_assigned(else_body, out);
            }
            Stmt::While { body, .. } => collect_assigned(body, out),
            Stmt::Assert(_) => {}
        }
    }
}

/// Check a block, threading the definite-assignment set through it.
fn check_stmts(
    spec: &Spec,
    prog: &[Stmt],
    definite: &mut HashSet<String>,
    depth: usize,
) -> Result<HashSet<String>, SemError> {
    if depth > 64 {
        return err("statement nesting too deep (max 64)");
    }
    let mut cur = definite.clone();
    for s in prog {
        match s {
            Stmt::Assign { name, value } => {
                check_assign_target(spec, name)?;
                let t = check_expr(value, &spec.params, &spec.locals, &spec.results, Some(&cur))?;
                let decl = lookup_var(spec, name)?;
                check_range_fits(&t, &decl, name)?;
                cur.insert(name.clone());
            }
            Stmt::ArrayAssign {
                array,
                index,
                value,
            } => {
                let _elem = lookup_array(array, &spec.params, &spec.locals, &spec.results)?;
                let it =
                    check_expr(index, &spec.params, &spec.locals, &spec.results, Some(&cur))?;
                if !matches!(it, Type::Int(_)) {
                    return err(format!("array index must be int, got `{}`", it));
                }
                let vt =
                    check_expr(value, &spec.params, &spec.locals, &spec.results, Some(&cur))?;
                if !matches!(vt, Type::Int(_)) {
                    return err(format!("array element must be int, got `{}`", vt));
                }
                cur.insert(array.clone());
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                let ct =
                    check_expr(cond, &spec.params, &spec.locals, &spec.results, Some(&cur))?;
                if ct != Type::Bool {
                    return err(format!("`if` condition must be bool, got `{}`", ct));
                }
                let mut t_set = cur.clone();
                let after_then = check_stmts(spec, then_body, &mut t_set, depth + 1)?;
                let mut e_set = cur.clone();
                let after_else = check_stmts(spec, else_body, &mut e_set, depth + 1)?;
                // After a branch, only what BOTH branches assigned is definite.
                cur = after_then.intersection(&after_else).cloned().collect();
            }
            Stmt::While {
                cond,
                invariants,
                decreases,
                body,
            } => {
                let ct =
                    check_expr(cond, &spec.params, &spec.locals, &spec.results, Some(&cur))?;
                if ct != Type::Bool {
                    return err(format!("`while` condition must be bool, got `{}`", ct));
                }
                for (i, inv) in invariants.iter().enumerate() {
                    let it =
                        check_expr(inv, &spec.params, &spec.locals, &spec.results, Some(&cur))?;
                    if it != Type::Bool {
                        return err(format!(
                            "loop invariant #{} must be bool, got `{}`: {}",
                            i + 1,
                            it,
                            inv
                        ));
                    }
                }
                if let Some(d) = decreases {
                    let dt =
                        check_expr(d, &spec.params, &spec.locals, &spec.results, Some(&cur))?;
                    if !matches!(dt, Type::Int(_)) {
                        return err(format!("`decreases` must be int, got `{}`", dt));
                    }
                }
                // Inside the body the invariant is *assumed*, so anything the
                // invariant mentions may be read. Conservative and sound.
                let mut body_set = cur.clone();
                for inv in invariants {
                    collect_names(inv, &mut body_set);
                }
                check_stmts(spec, body, &mut body_set, depth + 1)?;
                // After the loop only what was definite BEFORE stays definite
                // (the loop may execute zero times).
            }
            Stmt::Assert(e) => {
                let t = check_expr(e, &spec.params, &spec.locals, &spec.results, Some(&cur))?;
                if t != Type::Bool {
                    return err(format!("`assert` expects bool, got `{}`", t));
                }
            }
        }
    }
    *definite = cur.clone();
    Ok(cur)
}

/// Every variable name mentioned in an expression (used to relax the
/// definite-assignment set inside loop bodies, where the invariant is assumed).
fn collect_names(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Param(n) | Expr::Result(n) => {
            out.insert(n.clone());
        }
        Expr::ArrayRead(n, i) => {
            out.insert(n.clone());
            collect_names(i, out);
        }
        Expr::Len(_) => {}
        Expr::Unary(_, a) => collect_names(a, out),
        Expr::Binary(_, l, r) => {
            collect_names(l, out);
            collect_names(r, out);
        }
        Expr::Ite(c, a, b) => {
            collect_names(c, out);
            collect_names(a, out);
            collect_names(b, out);
        }
        Expr::Min(a, b) | Expr::Max(a, b) => {
            collect_names(a, out);
            collect_names(b, out);
        }
        Expr::Forall { lo, hi, body, .. }
        | Expr::Exists { lo, hi, body, .. }
        | Expr::Sum { lo, hi, body, .. } => {
            collect_names(lo, out);
            collect_names(hi, out);
            collect_names(body, out);
        }
        Expr::IntLit(_) | Expr::BoolLit(_) => {}
    }
}

/// A variable may be assigned unless it is a parameter (inputs are read-only).
fn check_assign_target(spec: &Spec, name: &str) -> Result<(), SemError> {
    if spec.params.iter().any(|b| b.name == name) {
        return err(format!(
            "cannot assign to parameter `{}` — inputs are read-only",
            name
        ));
    }
    if lookup_var(spec, name).is_ok() {
        Ok(())
    } else {
        err(format!(
            "assignment to undeclared variable `{}` — declare it in `locals (...)`",
            name
        ))
    }
}

fn lookup_var(spec: &Spec, name: &str) -> Result<Type, SemError> {
    for b in spec.locals.iter().chain(spec.results.iter()) {
        if b.name == name {
            return Ok(b.ty);
        }
    }
    err(format!("unknown variable `{}`", name))
}

/// Reject only *disjoint* ranges (definitely broken). Partial overlap is
/// deferred to the prover, which can use `requires`. A rejection here is a
/// static-analysis result; a violation there is a theorem.
fn check_range_fits(t: &Type, decl: &Type, name: &str) -> Result<(), SemError> {
    if let (Type::Int(expr_r), Type::Int(decl_r)) = (t, decl) {
        if expr_r.hi < decl_r.lo || expr_r.lo > decl_r.hi {
            return err(format!(
                "assignment to `{}`: expression ranges over {} which is disjoint from \
                 declared `{}` : {} — no input can make this fit",
                name, expr_r, name, decl
            ));
        }
    }
    Ok(())
}

/// Full semantic check of a spec, with an *external* body attached
/// (used by the synthesizer to vet candidates before bothering the prover).
pub fn analyze_with_body(spec: &Spec, body: &[Assign]) -> Result<(), SemError> {
    let mut with_body = spec.clone();
    with_body.body = Some(
        body.iter()
            .map(|a| Stmt::Assign {
                name: a.name.clone(),
                value: a.value.clone(),
            })
            .collect(),
    );
    analyze(&with_body)
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

    // Locals: unique, and must not shadow params or results.
    let mut lseen = HashSet::new();
    for l in &spec.locals {
        if !lseen.insert(l.name.as_str()) {
            return err(format!("duplicate local `{}`", l.name));
        }
        if seen.contains(l.name.as_str()) {
            return err(format!(
                "local `{}` shadows parameter `{}` — rename one; the name would mean two things",
                l.name, l.name
            ));
        }
        if rseen.contains(l.name.as_str()) {
            return err(format!(
                "local `{}` shadows result `{}` — rename one; the name would mean two things",
                l.name, l.name
            ));
        }
    }
    // An array-typed local is fine; an array-typed parameter is fine too.
    // Declared arrays are the only way `a[i]` can resolve, and
    // `lookup_array` reports anything else by name.

    if spec.params.is_empty() {
        return err("a spec needs at least one parameter");
    }
    if spec.results.is_empty() {
        return err("a spec needs at least one result");
    }

    // requires: over params only (locals don't exist yet).
    for e in &spec.requires {
        let t = check_expr(e, &spec.params, &[], &spec.results, None)?;
        if t != Type::Bool {
            return err(format!("`requires` must be bool, got `{}`: {}", t, e));
        }
    }

    // ensures: over params + results. Locals are internal state and are not
    // part of the contract — they may be mentioned only via the body.
    let all: HashSet<String> = spec.results.iter().map(|r| r.name.clone()).collect();
    for e in &spec.ensures {
        let t = check_expr(e, &spec.params, &[], &spec.results, Some(&all))?;
        if t != Type::Bool {
            return err(format!("`ensures` must be bool, got `{}`: {}", t, e));
        }
    }

    // Body: statements, with definite-assignment tracking.
    if let Some(body) = &spec.body {
        check_program(spec, body)?;
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
