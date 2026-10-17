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
//! upgrades that to **total correctness**. Without one, `probatum` says so instead
//! of quietly proving the weaker thing.

use crate::ast::*;

/// A proof obligation: `assumptions ⇒ goal`, quantified over every variable.
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

/// The variables an obligation quantifies over: only those it mentions.
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

/// Read-over-write substitution for `a[i] := e`.
///
/// A constant index replaces that element; a symbolic index uses the identity
/// `a[j] → ite(j == i, e, a[j])`.
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
        // but that kept stale reads after writes to `r` and accused correct programs.
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
        // Only mentioned variables range over their domains.
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
        self.wp_block_ctx(prog, post, &[])
    }

    /// This is the frame rule: an inner loop's exit obligation must see the
    /// outer body's facts, or correct programs become unprovable.
    fn wp_block_ctx(&mut self, prog: &[Stmt], post: Expr, ctx: &[Expr]) -> Expr {
        // mods[i] = every variable written by prog[0..i].
        let mut mods: Vec<std::collections::HashSet<String>> =
            Vec::with_capacity(prog.len() + 1);
        let mut cur: std::collections::HashSet<String> = std::collections::HashSet::new();
        mods.push(cur.clone());
        for s in prog {
            stmt_writes(s, &mut cur);
            mods.push(cur.clone());
        }

        let mut q = post;
        for i in (0..prog.len()).rev() {
            let live: Vec<Expr> = ctx
                .iter()
                .filter(|f| {
                    let mut fv = std::collections::HashSet::new();
                    free_vars(f, &mut fv);
                    fv.iter().all(|v| !mods[i].contains(v))
                })
                .cloned()
                .collect();
            q = self.wp_stmt_ctx(&prog[i], q, &live);
        }
        q
    }

    fn wp_stmt_ctx(&mut self, s: &Stmt, post: Expr, ctx: &[Expr]) -> Expr {
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
                let wp_then = self.wp_block_ctx(then_body, post.clone(), ctx);
                let wp_else = self.wp_block_ctx(else_body, post, ctx);
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

                // What is known when this guard is tested: the frame from the
                // enclosing scope, plus this loop's own invariant and guard.
                // For a loop at the top level the frame is empty and the three
                // obligations below are byte-for-byte what they were before.
                let mut exit_ctx: Vec<Expr> = ctx.to_vec();
                let mut guarded: Vec<Expr> = ctx.to_vec();
                guarded.push(inv.clone());
                guarded.push(cond.clone());

                // (1) Preservation: frame ∧ I ∧ guard ⇒ wp(body, I)
                let wp_body_inv = self.wp_block_ctx(body, inv.clone(), &guarded);
                self.push(
                    "loop preservation",
                    loc.clone(),
                    guarded.clone(),
                    wp_body_inv,
                );

                // (2) Exit: frame ∧ I ∧ ¬guard ⇒ post.
                let not_guard = Expr::Unary(UnOp::Not, Box::new(cond.clone()));
                exit_ctx.push(inv.clone());
                exit_ctx.push(not_guard);
                self.push("loop exit", loc.clone(), exit_ctx, post);

                // (3) Termination: frame ∧ I ∧ guard ⇒ decreases > 0 ∧ variant_after_body < decreases.
                if let Some(d) = decreases {
                    let after = variant_after(body, &d);
                    let decreased = Expr::Binary(
                        BinOp::Lt,
                        Box::new(after),
                        Box::new(d.clone()),
                    );
                    let positive = Expr::Binary(
                        BinOp::Gt,
                        Box::new(d.clone()),
                        Box::new(Expr::IntLit(0)),
                    );
                    self.push(
                        "loop termination",
                        loc.clone(),
                        guarded,
                        Expr::Binary(BinOp::And, Box::new(positive), Box::new(decreased)),
                    );
                }

                // The predicate that survives the loop is the invariant; the
                // obligations above are what license discarding ¬guard.
                inv
            }
        }
    }
}

/// How `d` reads after one execution of `body`.
///
/// A loop that writes none of the variant's variables is the identity on it;
/// otherwise it falls back to the invariant.
fn variant_after(body: &[Stmt], d: &Expr) -> Expr {
    let mut q = d.clone();
    for s in body {
        match s {
            Stmt::Assign { name, value } => q = subst_var(&q, name, value),
            Stmt::ArrayAssign { array, index, value } => {
                q = subst_array_write(&q, array, index, value)
            }
            Stmt::Assert(_) => {}
            Stmt::If { cond, then_body, else_body } => {
                let t = variant_after(then_body, &q);
                let e = variant_after(else_body, &q);
                q = Expr::Ite(Box::new(cond.clone()), Box::new(t), Box::new(e));
            }
            Stmt::While { invariants, .. } => {
                let mut writes = std::collections::HashSet::new();
                stmt_writes(s, &mut writes);
                let mut fv = std::collections::HashSet::new();
                free_vars(&q, &mut fv);
                if !fv.iter().all(|v| !writes.contains(v)) {
                    q = conjoin(invariants.clone());
                }
                // else: frame — the loop cannot move the variant, so it stays.
            }
        }
    }
    q
}

/// Every variable this statement writes, walking into branches and loop bodies.
///
/// Used by `wp_block_ctx` to keep a frame fact only while nothing could have
/// invalidated it: `c == i` may be assumed before a statement that writes `c`
/// and never after it.
fn stmt_writes(s: &Stmt, out: &mut std::collections::HashSet<String>) {
    match s {
        Stmt::Assign { name, .. } => {
            out.insert(name.clone());
        }
        Stmt::ArrayAssign { array, .. } => {
            out.insert(array.clone());
        }
        Stmt::Assert(_) => {}
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            for s in then_body {
                stmt_writes(s, out);
            }
            for s in else_body {
                stmt_writes(s, out);
            }
        }
        Stmt::While { body, .. } => {
            for s in body {
                stmt_writes(s, out);
            }
        }
    }
}

/// Generate every obligation for a spec + program.
///
/// The contract obligation is `requires ⇒ wp(program, ensures)`, quantified
/// over exactly its free variables.
pub fn obligations(spec: &Spec, prog: &Program) -> Vec<Obligation> {
    let mut gen = VcGen::new(spec);
    let post = conjoin(spec.ensures.clone());
    let wp = gen.wp_block(prog, post);
    let mut obs = gen.obligations;

    // The contract obligation quantifies over exactly the free variables of the
    // weakest precondition.
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
