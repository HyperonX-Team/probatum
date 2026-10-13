//! Hoare-logic verification-condition generation.
//!
//! Loops cannot be verified by evaluation alone — a loop is an *infinite*
//! family of executions, and testing it is exactly the thing that doesn't
//! work. The classical answer is an **inductive invariant**: a property that
//! holds on entry, is preserved by every iteration, and implies the
//! postcondition on exit. That invariant *is* the intent for the loop, which
//! is why this language requires one.
//!
//! This module turns a program into a list of **obligations** — universally
//! quantified implications over the program's variables:
//!
//! ```text
//! obligation := (assumptions) ⇒ (goal)
//! ```
//!
//! Each obligation is discharged by the ordinary proof engines (they already
//! answer "does this hold for every value in these domains?"), which is what
//! makes loops provable without a new solver:
//!
//! * **Contract**:      `requires ⇒ wp(program, ensures)`
//! * **Entry**:         `I` established before the loop
//! * **Preservation**:  `I ∧ guard ⇒ wp(body, I)`
//! * **Exit**:          `I ∧ ¬guard ⇒ Q`
//! * **Termination**:   `I ∧ guard ⇒ decreases > 0 ∧ wp(body, decreases) < decreases`
//!
//! ## What "proved" means with loops
//!
//! *Preservation* and *exit* together give **partial correctness**: if the
//! loop terminates, the postcondition holds. Adding a `decreases` clause
//! upgrades that to **total correctness**. Without one, `ic` says so instead
//! of quietly proving the weaker thing.

use crate::ast::*;

/// A proof obligation: `assumptions ⇒ goal`, universally quantified over
/// every variable in scope.
#[derive(Clone, Debug)]
pub struct Obligation {
    /// Short label: "contract", "loop entry", "loop preservation", …
    pub kind: String,
    /// Where it came from, for error messages.
    pub location: String,
    pub assumptions: Vec<Expr>,
    pub goal: Expr,
    /// Variables this obligation quantifies over (name + domain), in the
    /// canonical order the engines enumerate.
    pub vars: Vec<Binding>,
}

impl std::fmt::Display for Obligation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let a: Vec<String> = self.assumptions.iter().map(|e| e.to_string()).collect();
        write!(
            f,
            "{} [{}]: ({}) ⇒ ({})",
            self.kind,
            self.location,
            if a.is_empty() {
                "true".to_string()
            } else {
                a.join(" ∧ ")
            },
            self.goal
        )
    }
}

/// Conjunction of expressions (empty ⇒ `true`).
pub fn conjoin(mut es: Vec<Expr>) -> Expr {
    if es.is_empty() {
        return Expr::BoolLit(true);
    }
    let mut acc = es.remove(0);
    for e in es {
        acc = Expr::Binary(BinOp::And, Box::new(acc), Box::new(e));
    }
    acc
}

/// Substitute a variable by an expression, respecting quantifier shadowing.
pub fn subst_var(e: &Expr, name: &str, replacement: &Expr) -> Expr {
    match e {
        Expr::Param(n) | Expr::Result(n) if n == name => replacement.clone(),
        Expr::Param(_) | Expr::Result(_) | Expr::IntLit(_) | Expr::BoolLit(_) => e.clone(),
        Expr::Unary(op, a) => Expr::Unary(*op, Box::new(subst_var(a, name, replacement))),
        Expr::Binary(op, l, r) => Expr::Binary(
            *op,
            Box::new(subst_var(l, name, replacement)),
            Box::new(subst_var(r, name, replacement)),
        ),
        Expr::Ite(c, a, b) => Expr::Ite(
            Box::new(subst_var(c, name, replacement)),
            Box::new(subst_var(a, name, replacement)),
            Box::new(subst_var(b, name, replacement)),
        ),
        Expr::Min(a, b) => Expr::Min(
            Box::new(subst_var(a, name, replacement)),
            Box::new(subst_var(b, name, replacement)),
        ),
        Expr::Max(a, b) => Expr::Max(
            Box::new(subst_var(a, name, replacement)),
            Box::new(subst_var(b, name, replacement)),
        ),
        Expr::ArrayRead(n, i) => Expr::ArrayRead(
            n.clone(),
            Box::new(subst_var(i, name, replacement)),
        ),
        Expr::Len(n) => Expr::Len(n.clone()),
        Expr::Forall { var, lo, hi, body } => Expr::Forall {
            var: var.clone(),
            lo: Box::new(subst_var(lo, name, replacement)),
            hi: Box::new(subst_var(hi, name, replacement)),
            // Do not substitute under a binder that shadows `name`.
            body: if var == name {
                body.clone()
            } else {
                Box::new(subst_var(body, name, replacement))
            },
        },
        Expr::Exists { var, lo, hi, body } => Expr::Exists {
            var: var.clone(),
            lo: Box::new(subst_var(lo, name, replacement)),
            hi: Box::new(subst_var(hi, name, replacement)),
            body: if var == name {
                body.clone()
            } else {
                Box::new(subst_var(body, name, replacement))
            },
        },
        Expr::Sum { var, lo, hi, body } => Expr::Sum {
            var: var.clone(),
            lo: Box::new(subst_var(lo, name, replacement)),
            hi: Box::new(subst_var(hi, name, replacement)),
            body: if var == name {
                body.clone()
            } else {
                Box::new(subst_var(body, name, replacement))
            },
        },
    }
}

/// The variables an obligation quantifies over: only those it actually
/// mentions. Restricting to the free variables is sound (an unmentioned
/// variable cannot affect the truth of the implication) and it shrinks the
/// state space dramatically — a loop proof that names three variables should
/// not be enumerated over the whole program's state.
fn scope_vars(spec: &Spec, exprs: &[&Expr]) -> Vec<Binding> {
    let mut free: std::collections::HashSet<String> = std::collections::HashSet::new();
    for e in exprs {
        free_vars(e, &mut free);
    }
    spec.all_vars()
        .into_iter()
        .filter(|b| free.contains(&b.name))
        .collect()
}

/// Collect free variable names, respecting quantifier binding.
fn free_vars(e: &Expr, out: &mut std::collections::HashSet<String>) {
    match e {
        Expr::Param(n) | Expr::Result(n) => {
            out.insert(n.clone());
        }
        Expr::ArrayRead(n, i) => {
            out.insert(n.clone());
            free_vars(i, out);
        }
        Expr::Len(n) => {
            out.insert(n.clone());
        }
        Expr::Unary(_, a) => free_vars(a, out),
        Expr::Binary(_, l, r) => {
            free_vars(l, out);
            free_vars(r, out);
        }
        Expr::Ite(c, a, b) => {
            free_vars(c, out);
            free_vars(a, out);
            free_vars(b, out);
        }
        Expr::Min(a, b) | Expr::Max(a, b) => {
            free_vars(a, out);
            free_vars(b, out);
        }
        Expr::Forall { var, lo, hi, body }
        | Expr::Exists { var, lo, hi, body }
        | Expr::Sum { var, lo, hi, body } => {
            free_vars(lo, out);
            free_vars(hi, out);
            let mut inner = std::collections::HashSet::new();
            free_vars(body, &mut inner);
            inner.remove(var); // bound, not free
            out.extend(inner);
        }
        Expr::IntLit(_) | Expr::BoolLit(_) => {}
    }
}

/// The variables an obligation quantifies over: every parameter, local and
/// result, in canonical order.
fn scope_vars_all(spec: &Spec) -> Vec<Binding> {
    spec.all_vars()
}

/// Read-over-write substitution for `a[i] := e`.
///
/// A *constant* index replaces exactly that element. A *symbolic* index is
/// handled by the exact bounded-array identity
/// `a[j] → ite(j == i, e, a[j])` — after a write at `i`, reading `j` yields
/// the new value iff `j == i`. This is how array assignment becomes a pure
/// expression without inventing a theory of arrays.
fn subst_array_write(e: &Expr, array: &str, index: &Expr, value: &Expr) -> Expr {
    match e {
        Expr::ArrayRead(n, j) if n == array => {
            // ite(j == index, value, a[j])
            let j_sub = subst_array_write(j, array, index, value);
            let cond = Expr::Binary(
                BinOp::Eq,
                Box::new(j_sub.clone()),
                Box::new(index.clone()),
            );
            Expr::Ite(
                Box::new(cond),
                Box::new(value.clone()),
                Box::new(Expr::ArrayRead(n.clone(), Box::new(j_sub))),
            )
        }
        Expr::ArrayRead(_, i) => {
            Expr::ArrayRead(
                match e {
                    Expr::ArrayRead(n, _) => n.clone(),
                    _ => unreachable!(),
                },
                Box::new(subst_array_write(i, array, index, value)),
            )
        }
        Expr::Param(_) | Expr::Result(_) | Expr::IntLit(_) | Expr::BoolLit(_) => e.clone(),
        Expr::Unary(op, a) => {
            Expr::Unary(*op, Box::new(subst_array_write(a, array, index, value)))
        }
        Expr::Binary(op, l, r) => Expr::Binary(
            *op,
            Box::new(subst_array_write(l, array, index, value)),
            Box::new(subst_array_write(r, array, index, value)),
        ),
        Expr::Ite(c, a, b) => Expr::Ite(
            Box::new(subst_array_write(c, array, index, value)),
            Box::new(subst_array_write(a, array, index, value)),
            Box::new(subst_array_write(b, array, index, value)),
        ),
        Expr::Min(a, b) => Expr::Min(
            Box::new(subst_array_write(a, array, index, value)),
            Box::new(subst_array_write(b, array, index, value)),
        ),
        Expr::Max(a, b) => Expr::Max(
            Box::new(subst_array_write(a, array, index, value)),
            Box::new(subst_array_write(b, array, index, value)),
        ),
        Expr::Len(n) => Expr::Len(n.clone()),
        // Recurse into quantifier bodies too. An earlier version skipped them,
        // reasoning that a bound variable might shadow the write's index —
        // but the type checker already rejects shadowing, and skipping meant
        // `forall i in 0..3: r[i] == ...` kept its OLD `r[i]` after the writes
        // to `r`, so a correct program was accused of violating its contract.
        Expr::Forall { var, lo, hi, body } => Expr::Forall {
            var: var.clone(),
            lo: Box::new(subst_array_write(lo, array, index, value)),
            hi: Box::new(subst_array_write(hi, array, index, value)),
            body: Box::new(subst_array_write(body, array, index, value)),
        },
        Expr::Exists { var, lo, hi, body } => Expr::Exists {
            var: var.clone(),
            lo: Box::new(subst_array_write(lo, array, index, value)),
            hi: Box::new(subst_array_write(hi, array, index, value)),
            body: Box::new(subst_array_write(body, array, index, value)),
        },
        Expr::Sum { var, lo, hi, body } => Expr::Sum {
            var: var.clone(),
            lo: Box::new(subst_array_write(lo, array, index, value)),
            hi: Box::new(subst_array_write(hi, array, index, value)),
            body: Box::new(subst_array_write(body, array, index, value)),
        },
    }
}

/// Accumulator for obligations discovered while walking backwards.
pub struct VcGen<'a> {
    pub spec: &'a Spec,
    pub obligations: Vec<Obligation>,
}

impl<'a> VcGen<'a> {
    pub fn new(spec: &'a Spec) -> Self {
        VcGen {
            spec,
            obligations: Vec::new(),
        }
    }

    fn push(&mut self, kind: &str, location: String, assumptions: Vec<Expr>, goal: Expr) {
        // Only the variables this obligation actually mentions need to range
        // over their domains — an unmentioned variable cannot change the
        // truth of the implication, and leaving it out keeps the state space
        // small enough for the exhaustive engine to decide the obligation.
        let refs: Vec<&Expr> = assumptions.iter().chain(std::iter::once(&goal)).collect();
        let vars = scope_vars(self.spec, &refs);
        self.obligations.push(Obligation {
            kind: kind.to_string(),
            location,
            assumptions,
            goal,
            vars,
        });
    }

    /// Weakest precondition of a statement block with respect to `post`.
    pub fn wp_block(&mut self, prog: &[Stmt], post: Expr) -> Expr {
        let mut q = post;
        // Backwards: the last statement's wp is applied first.
        for s in prog.iter().rev() {
            q = self.wp_stmt(s, q);
        }
        q
    }

    fn wp_stmt(&mut self, s: &Stmt, post: Expr) -> Expr {
        match s {
            Stmt::Assign { name, value } => subst_var(&post, name, value),

            Stmt::ArrayAssign {
                array,
                index,
                value,
            } => subst_array_write(&post, array, index, value),

            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                let wp_then = self.wp_block(then_body, post.clone());
                let wp_else = self.wp_block(else_body, post);
                // ite(cond, wp_then, wp_else)
                Expr::Ite(
                    Box::new(cond.clone()),
                    Box::new(wp_then),
                    Box::new(wp_else),
                )
            }

            Stmt::Assert(e) => {
                // `assert e` means: e holds here, and then the rest.
                Expr::Binary(BinOp::And, Box::new(e.clone()), Box::new(post))
            }

            Stmt::While {
                cond,
                invariants,
                decreases,
                body,
            } => {
                let inv = conjoin(invariants.clone());
                let loc = format!("while {} ", cond);

                // (1) Preservation: I ∧ guard ⇒ wp(body, I)
                let wp_body_inv = self.wp_block(body, inv.clone());
                self.push(
                    "loop preservation",
                    loc.clone(),
                    vec![inv.clone(), cond.clone()],
                    wp_body_inv,
                );

                // (2) Exit: I ∧ ¬guard ⇒ post
                let not_guard = Expr::Unary(UnOp::Not, Box::new(cond.clone()));
                self.push(
                    "loop exit",
                    loc.clone(),
                    vec![inv.clone(), not_guard.clone()],
                    post,
                );

                // (3) Termination, when a variant is given:
                //     I ∧ guard ⇒ decreases > 0 ∧ wp(body, decreases) < decreases
                if let Some(d) = decreases {
                    let after = self.wp_block(body, d.clone());
                    let positive = Expr::Binary(
                        BinOp::Gt,
                        Box::new(d.clone()),
                        Box::new(Expr::IntLit(0)),
                    );
                    let decreased = Expr::Binary(
                        BinOp::Lt,
                        Box::new(after),
                        Box::new(d.clone()),
                    );
                    self.push(
                        "loop termination",
                        loc.clone(),
                        vec![inv.clone(), cond.clone()],
                        Expr::Binary(BinOp::And, Box::new(positive), Box::new(decreased)),
                    );
                }

                // The predicate that survives the loop is the invariant; the
                // two obligations above are what license discarding ¬guard.
                inv
            }
        }
    }
}

/// Generate every obligation for a spec + program.
///
/// The first obligation is always the top-level contract:
/// `requires ⇒ wp(program, ensures)`.
pub fn obligations(spec: &Spec, prog: &Program) -> Vec<Obligation> {
    let mut gen = VcGen::new(spec);
    let post = conjoin(spec.ensures.clone());
    let wp = gen.wp_block(prog, post);
    let mut obs = gen.obligations;

    // The contract obligation is `requires ⇒ wp(program, ensures)`. The
    // weakest precondition mentions whatever the program touches — locals
    // included — so it is quantified over exactly its free variables. That
    // is both correct and minimal: an unmentioned variable cannot change the
    // truth of the implication.
    let mut free = std::collections::HashSet::new();
    for e in &spec.requires {
        free_vars(e, &mut free);
    }
    free_vars(&wp, &mut free);
    let vars: Vec<Binding> = spec
        .all_vars()
        .into_iter()
        .filter(|b| free.contains(&b.name))
        .collect();

    obs.insert(
        0,
        Obligation {
            kind: "contract".to_string(),
            location: "spec".to_string(),
            assumptions: spec.requires.clone(),
            goal: wp,
            vars,
        },
    );
    obs
}

/// Does the program contain a loop without a `decreases` clause?
/// (Used to report honestly that termination is *not* proven.)
pub fn has_unproven_termination(prog: &[Stmt]) -> bool {
    prog.iter().any(|s| match s {
        Stmt::While { decreases, body, .. } => {
            decreases.is_none() || has_unproven_termination(body)
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => has_unproven_termination(then_body) || has_unproven_termination(else_body),
        _ => false,
    })
}
