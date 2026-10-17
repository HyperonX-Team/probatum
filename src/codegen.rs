//! Code generation: a *verified* program → real code in a target language.
//!
//! The generated function is the synthesizer's output plus the contract as
//! runtime checks (like `debug_assert` in Rust, `panic` guards in Go), and
//! a comment carrying the certificate digest — so the code you ship can
//! always be traced back to the proof that blessed it.
//!
//! Important honesty note: generated runtime guards are a *backstop*, not
//! the proof. The proof is the certificate; the guards catch drift if
//! someone calls the function outside its verified envelope.

use crate::ast::*;

#[derive(Clone, Copy)]
pub enum TargetLang {
    Rust,
    Go,
    Dsl,
}

impl TargetLang {
    pub fn from_name(s: &str) -> Option<Self> {
        match s {
            "rust" | "rs" => Some(TargetLang::Rust),
            "go" | "golang" => Some(TargetLang::Go),
            "dsl" | "ic" => Some(TargetLang::Dsl),
            _ => None,
        }
    }

    pub fn file_extension(&self) -> &'static str {
        match self {
            TargetLang::Rust => "rs",
            TargetLang::Go => "go",
            TargetLang::Dsl => "ic",
        }
    }
}

/// Render an expression in the target language's syntax.
fn emit_expr(e: &Expr, lang: TargetLang) -> String {
    match lang {
        TargetLang::Go => emit_expr_go(e),
        TargetLang::Rust => rust_expr(e, 0),
        TargetLang::Dsl => emit_expr_rust_like(e),
    }
}

/// Rust operator precedence for the emitted subset — HIGHER BINDS TIGHTER.
///
/// Mirrors rustc exactly. This is not a style choice: the emitted code must
/// group *exactly* as the expression tree the prover verified, or the shipped
/// code would not be the thing that was proven.
fn rust_prec(e: &Expr) -> u8 {
    match e {
        Expr::Binary(op, ..) => match op {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 3,
            BinOp::Add | BinOp::Sub => 4,
            BinOp::Mul | BinOp::Div | BinOp::Mod => 5,
        },
        // `if` and quantifier blocks; valid bare as operands only in trivial
        // cases, so they group below everything and parenthesize on demand.
        Expr::Ite(..) | Expr::Forall { .. } | Expr::Exists { .. } | Expr::Sum { .. } => 0,
        // Names, literals, method-call chains, indexing, `as` chains: bind
        // tighter than anything emitted above.
        _ => 6,
    }
}

fn rust_binop_spelling(op: BinOp) -> &'static str {
    match op {
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Le => "<=",
        BinOp::Ge => ">=",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::And => "&&",
        BinOp::Or => "||",
    }
}

/// Can `e` stand bare immediately before a `.method(...)`?
///
/// Postfix (method call, index) binds tighter than any infix operator, so
/// names, literals, booleans and index chains qualify. A *negative* literal
/// does not — `.min` would bind to the absolute value, silently swapping
/// `(-1).min(y)` for `-(1.min(y))` — and neither does `Len`, whose `as i64`
/// cast sits BELOW postfix: `x.len() as i64.min(y)` attaches `.min` to the
/// type, which does not compile.
fn rust_is_postfix_operand(e: &Expr) -> bool {
    match e {
        Expr::Param(_) | Expr::BoolLit(_) | Expr::ArrayRead(..) => true,
        Expr::IntLit(v) => *v >= 0,
        _ => false,
    }
}

/// Render `e` in Rust, parenthesized ONLY where rustc's precedence would
/// otherwise group differently from the tree the prover verified.
///
/// `min_prec` is the lowest precedence allowed to stand bare in this
/// position; anything looser gets the parentheses it needs — no more, no
/// less. That restraint is also what keeps `unused_parens` silent in the
/// generated code: every paren here is a load-bearing one.
fn rust_expr(e: &Expr, min_prec: u8) -> String {
    let body = match e {
        Expr::IntLit(v) => v.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Param(n) | Expr::Result(n) => n.clone(),
        Expr::Unary(op, a) => {
            let s = rust_expr(a, 6);
            // Defensive: adjacent unary operators (`--1`) parse but read as a
            // mistake; grouping costs one paren and nothing else.
            let s = if matches!(a.as_ref(), Expr::Unary(..)) {
                format!("({s})")
            } else {
                s
            };
            match op {
                UnOp::Neg => format!("-{s}"),
                UnOp::Not => format!("!{s}"),
            }
        }
        Expr::Binary(op, l, r) => {
            // Left-associative: the left child may share the parent's
            // precedence (`a - b - c` == `(a - b) - c`), the right child may
            // not (`a - (b - c)` keeps its group).
            let p = rust_prec(e);
            let l = rust_expr(l, p);
            let r = rust_expr(r, p + 1);
            format!("{l} {} {r}", rust_binop_spelling(*op))
        }
        Expr::Ite(c, a, b) => format!(
            "if {} {{ {} }} else {{ {} }}",
            rust_expr(c, 0),
            rust_expr(a, 0),
            rust_expr(b, 0)
        ),
        Expr::Min(a, b) | Expr::Max(a, b) => {
            let m = if matches!(e, Expr::Min(..)) { "min" } else { "max" };
            let recv = if rust_is_postfix_operand(a) {
                rust_expr(a, 0)
            } else {
                format!("({})", rust_expr(a, 0))
            };
            format!("{recv}.{m}({})", rust_expr(b, 0))
        }
        Expr::ArrayRead(n, i) => {
            let plain = rust_expr(i, 0);
            let idx = match i.as_ref() {
                Expr::Param(_) | Expr::IntLit(_) => format!("{plain} as usize"),
                _ => format!("({plain}) as usize"),
            };
            format!("{n}[{idx}]")
        }
        Expr::Len(n) => format!("{n}.len() as i64"),
        Expr::Forall { var, lo, hi, body } => format!(
            "{{ let mut ok = true; let __lo = {lo}; let __hi = {hi}; \
             for {v} in __lo..=__hi {{ if !({b}) {{ ok = false; break; }} }} ok }}",
            lo = rust_expr(lo, 0),
            hi = rust_expr(hi, 0),
            v = var,
            b = rust_expr(body, 6),
        ),
        Expr::Exists { var, lo, hi, body } => format!(
            "{{ let mut found = false; let __lo = {lo}; let __hi = {hi}; \
             for {v} in __lo..=__hi {{ if {b} {{ found = true; break; }} }} found }}",
            lo = rust_expr(lo, 0),
            hi = rust_expr(hi, 0),
            v = var,
            b = rust_expr(body, 0),
        ),
        Expr::Sum { var, lo, hi, body } => format!(
            "{{ let mut acc: i64 = 0; let __lo = {lo}; let __hi = {hi}; \
             for {v} in __lo..=__hi {{ acc += {b}; }} acc }}",
            lo = rust_expr(lo, 0),
            hi = rust_expr(hi, 0),
            v = var,
            b = rust_expr(body, 0),
        ),
    };
    if rust_prec(e) < min_prec {
        format!("({body})")
    } else {
        body
    }
}

fn emit_expr_rust_like(e: &Expr) -> String {
    match e {
        Expr::IntLit(v) => v.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Param(n) => n.clone(),
        Expr::Result(n) => n.clone(), // in body context, results are locals
        Expr::Unary(UnOp::Neg, a) => format!("-({})", emit_expr_rust_like(a)),
        Expr::Unary(UnOp::Not, a) => format!("!({})", emit_expr_rust_like(a)),
        Expr::Binary(op, l, r) => {
            // Rust operator spelling for our subset (all are valid Rust infix).
            let o = match op {
                BinOp::Eq => "==",
                BinOp::Ne => "!=",
                BinOp::Le => "<=",
                BinOp::Ge => ">=",
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::Mod => "%",
                BinOp::Lt => "<",
                BinOp::Gt => ">",
                BinOp::And => "&&",
                BinOp::Or => "||",
            };
            format!(
                "({} {} {})",
                emit_expr_rust_like(l),
                o,
                emit_expr_rust_like(r)
            )
        }
        Expr::Ite(c, a, b) => format!(
            "(if {} {{ {} }} else {{ {} }})",
            emit_expr_rust_like(c),
            emit_expr_rust_like(a),
            emit_expr_rust_like(b)
        ),
        Expr::Min(a, b) => format!(
            "(({}).min({}))",
            emit_expr_rust_like(a),
            emit_expr_rust_like(b)
        ),
        Expr::Max(a, b) => format!(
            "(({}).max({}))",
            emit_expr_rust_like(a),
            emit_expr_rust_like(b)
        ),
        // arrays, quantifiers, folds
        // Emitted as inline blocks so the result is a plain expression, which
        // keeps generated code readable and avoids inventing helper names.
        Expr::ArrayRead(n, i) => format!("{}[({}) as usize]", n, emit_expr_rust_like(i)),
        Expr::Len(n) => format!("({}.len() as i64)", n),
        Expr::Forall { var, lo, hi, body } => format!(
            "{{ let mut ok = true; let __lo = {lo}; let __hi = {hi}; \
             for {v} in __lo..=__hi {{ if !({b}) {{ ok = false; break; }} }} ok }}",
            lo = emit_expr_rust_like(lo),
            hi = emit_expr_rust_like(hi),
            v = var,
            b = emit_expr_rust_like(body)
        ),
        Expr::Exists { var, lo, hi, body } => format!(
            "{{ let mut found = false; let __lo = {lo}; let __hi = {hi}; \
             for {v} in __lo..=__hi {{ if {b} {{ found = true; break; }} }} found }}",
            lo = emit_expr_rust_like(lo),
            hi = emit_expr_rust_like(hi),
            v = var,
            b = emit_expr_rust_like(body)
        ),
        Expr::Sum { var, lo, hi, body } => format!(
            "{{ let mut acc: i64 = 0; let __lo = {lo}; let __hi = {hi}; \
             for {v} in __lo..=__hi {{ acc += {b}; }} acc }}",
            lo = emit_expr_rust_like(lo),
            hi = emit_expr_rust_like(hi),
            v = var,
            b = emit_expr_rust_like(body)
        ),
    }
}

fn emit_expr_go(e: &Expr) -> String {
    match e {
        Expr::IntLit(v) => v.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Param(n) => n.clone(),
        Expr::Result(n) => n.clone(),
        Expr::Unary(UnOp::Neg, a) => format!("-({})", emit_expr_go(a)),
        Expr::Unary(UnOp::Not, a) => format!("!({})", emit_expr_go(a)),
        Expr::Binary(op, l, r) => {
            let o = match op {
                BinOp::Eq => "==",
                BinOp::Ne => "!=",
                BinOp::Le => "<=",
                BinOp::Ge => ">=",
                BinOp::Div => "/",
                BinOp::Mod => "%",
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Lt => "<",
                BinOp::Gt => ">",
                BinOp::And => "&&",
                BinOp::Or => "||",
            };
            format!("({} {} {})", emit_expr_go(l), o, emit_expr_go(r))
        }
        // Go has no ternary; use a closure call.
        Expr::Ite(c, a, b) => format!(
            "func() int64 {{ if {} {{ return {} }}; return {} }}()",
            emit_expr_go(c),
            emit_expr_go(a),
            emit_expr_go(b)
        ),
        Expr::Min(a, b) => {
            let (x, y) = (emit_expr_go(a), emit_expr_go(b));
            format!("func() int64 {{ if {} < {} {{ return {} }}; return {} }}()", x, y, x, y)
        }
        Expr::Max(a, b) => {
            let (x, y) = (emit_expr_go(a), emit_expr_go(b));
            format!("func() int64 {{ if {} > {} {{ return {} }}; return {} }}()", x, y, x, y)
        }
        // arrays, quantifiers, folds
        Expr::ArrayRead(n, i) => format!("{}[{}]", n, emit_expr_go(i)),
        Expr::Len(n) => format!("int64(len({}))", n),
        Expr::Forall { var, lo, hi, body } => format!(
            "func() bool {{ for {v} := {lo}; {v} <= {hi}; {v}++ {{ if !({b}) {{ return false }} }}; return true }}()",
            v = var,
            lo = emit_expr_go(lo),
            hi = emit_expr_go(hi),
            b = emit_expr_go(body)
        ),
        Expr::Exists { var, lo, hi, body } => format!(
            "func() bool {{ for {v} := {lo}; {v} <= {hi}; {v}++ {{ if {b} {{ return true }} }}; return false }}()",
            v = var,
            lo = emit_expr_go(lo),
            hi = emit_expr_go(hi),
            b = emit_expr_go(body)
        ),
        Expr::Sum { var, lo, hi, body } => format!(
            "func() int64 {{ var acc int64 = 0; for {v} := {lo}; {v} <= {hi}; {v}++ {{ acc += {b} }}; return acc }}()",
            v = var,
            lo = emit_expr_go(lo),
            hi = emit_expr_go(hi),
            b = emit_expr_go(body)
        ),
    }
}

fn rust_ty(t: &Type) -> String {
    match t {
        Type::Int(_) => "i64".into(),
        Type::Bool => "bool".into(),
        Type::Decimal { .. } => "i64".into(), // scaled integer — exact
        Type::Array { .. } => "Vec<i64>".into(),
    }
}

fn go_ty(t: &Type) -> String {
    match t {
        Type::Int(_) => "int64".into(),
        Type::Bool => "bool".into(),
        Type::Decimal { .. } => "int64".into(),
        Type::Array { .. } => "[]int64".into(),
    }
}

/// Generate a full compilation unit for `spec` + verified program.
pub fn emit(
    spec: &Spec,
    prog: &Program,
    lang: TargetLang,
    cert_digest: &str,
) -> Result<String, String> {
    match lang {
        TargetLang::Dsl => Ok(emit_dsl(spec, prog, cert_digest)),
        TargetLang::Rust => Ok(emit_rust(spec, prog, cert_digest)),
        TargetLang::Go => Ok(emit_go(spec, prog, cert_digest)),
    }
}

/// Emit a statement block in the target language.
///
/// Every variable is declared up front (see the emitters), so statements are
/// plain assignments in both languages — which is also what makes
/// reassignment inside a loop correct in Go, where `:=` would shadow.
fn emit_stmts(stmts: &[Stmt], lang: TargetLang, indent: usize, let_for: &[String]) -> String {
    let pad = "    ".repeat(indent);
    let mut s = String::new();
    for st in stmts {
        match st {
            Stmt::Assign { name, value } => {
                match lang {
                    // Straight-line results become declarations AT the
                    // assignment: there is exactly one write and the machine
                    // never reads a result before it, so pre-declaring a
                    // different value would only be a dead store rustc
                    // rightly complains about.
                    TargetLang::Rust if let_for.iter().any(|t| t == name) => {
                        s.push_str(&format!("{}let {} = {};\n", pad, name, rust_expr(value, 0)));
                    }
                    _ => {
                        s.push_str(&format!(
                            "{}{} = {};\n",
                            pad,
                            name,
                            emit_expr(value, lang)
                        ));
                    }
                }
            }
            Stmt::ArrayAssign {
                array,
                index,
                value,
            } => {
                s.push_str(&format!(
                    "{}{}[{}] = {};\n",
                    pad,
                    array,
                    emit_expr(index, lang),
                    emit_expr(value, lang)
                ));
            }
            Stmt::Assert(e) => {
                // The runtime backstop for an inline proof obligation.
                let cond = emit_expr(e, lang);
                match lang {
                    TargetLang::Go => {
                        s.push_str(&format!(
                            "{}if !({}) {{ panic(\"assertion failed\") }}\n",
                            pad, cond
                        ));
                    }
                    _ => {
                        s.push_str(&format!("{}debug_assert!({});\n", pad, cond));
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                s.push_str(&format!("{}if {} {{\n", pad, emit_expr(cond, lang)));
                s.push_str(&emit_stmts(then_body, lang, indent + 1, let_for));
                if else_body.is_empty() {
                    s.push_str(&format!("{}}}\n", pad));
                } else {
                    s.push_str(&format!("{}}} else {{\n", pad));
                    s.push_str(&emit_stmts(else_body, lang, indent + 1, let_for));
                    s.push_str(&format!("{}}}\n", pad));
                }
            }
            Stmt::While { cond, body, .. } => {
                s.push_str(&format!("{}while {} {{\n", pad, emit_expr(cond, lang)));
                s.push_str(&emit_stmts(body, lang, indent + 1, let_for));
                s.push_str(&format!("{}}}\n", pad));
            }
        }
    }
    s
}

fn emit_dsl(spec: &Spec, prog: &Program, cert_digest: &str) -> String {
    let mut s = String::new();
    s.push_str(&format!(
        "// Generated by probatum (the intent compiler)\n// verified-by-cert-sha256: {}\n",
        cert_digest
    ));
    s.push_str(&format!("spec {}(", spec.name));
    s.push_str(
        &spec
            .params
            .iter()
            .map(|b| format!("{}: {}", b.name, b.ty))
            .collect::<Vec<_>>()
            .join(", "),
    );
    s.push_str(")\n  returns (");
    s.push_str(
        &spec
            .results
            .iter()
            .map(|b| format!("{}: {}", b.name, b.ty))
            .collect::<Vec<_>>()
            .join(", "),
    );
    s.push_str(")\n");
    for c in &spec.requires {
        s.push_str(&format!("  requires {}\n", c));
    }
    for c in &spec.ensures {
        s.push_str(&format!("  ensures {}\n", c));
    }
    for e in &spec.examples {
        let ins: Vec<String> = e.inputs.iter().map(|v| v.to_string()).collect();
        let outs: Vec<String> = e.outputs.iter().map(|v| v.to_string()).collect();
        s.push_str(&format!(
            "  example ({}) => ({})\n",
            ins.join(", "),
            outs.join(", ")
        ));
    }
    s.push_str("{\n");
    // Canonical statement rendering — the same text the certificate digests,
    // so the artifact and the proof always describe the same program.
    s.push_str(&crate::ast::render_program_stmts(prog, 1));
    s.push_str("}\n");
    s
}

// dead-initializer avoidance
//
// The verifier's semantics give every local and result a defined value from
// the moment of entry: the bottom of its declared domain. In generated code
// that becomes an initializer — unless the program provably overwrites the
// variable before any read, in which case the initializer is a dead store
// rustc rightly flags.
//
// The trigger is a *first-touch* scan over the program in execution order.
// Top-level statements always run, in order — control flow only nests
// *within* them — so when the first mention of a variable is a top-level
// write, no later read can ever observe the initial value. Any other first
// touch (a read, or a write nested inside `if`/`while` that some
// executions skip) keeps the initializer: the prover may well have reasoned
// about it, and dropping it would change the verified semantics.
const TOUCH_TOPWRITE: u8 = 0; // unconditionally written before anything else
const TOUCH_NESTED_WRITE: u8 = 1; // first write exists but some runs skip it
const TOUCH_READ: u8 = 2; // read before any write: the initial value matters

fn first_touch_scan(prog: &Program) -> std::collections::HashMap<String, u8> {
    fn expr_reads(e: &Expr, out: &mut Vec<String>) {
        match e {
            Expr::Param(n) | Expr::Result(n) => out.push(n.clone()),
            Expr::ArrayRead(_, i) => expr_reads(i, out),
            Expr::Len(_) => {}
            Expr::Unary(_, a) => expr_reads(a, out),
            Expr::Binary(_, l, r) => {
                expr_reads(l, out);
                expr_reads(r, out);
            }
            Expr::Ite(c, a, b) => {
                expr_reads(c, out);
                expr_reads(a, out);
                expr_reads(b, out);
            }
            Expr::Min(a, b) | Expr::Max(a, b) => {
                expr_reads(a, out);
                expr_reads(b, out);
            }
            Expr::Forall { lo, hi, body, .. }
            | Expr::Exists { lo, hi, body, .. }
            | Expr::Sum { lo, hi, body, .. } => {
                expr_reads(lo, out);
                expr_reads(hi, out);
                expr_reads(body, out);
            }
            Expr::IntLit(_) | Expr::BoolLit(_) => {}
        }
    }
    fn scan(
        prog: &[Stmt],
        out: &mut std::collections::HashMap<String, u8>,
        top: bool,
    ) {
        for st in prog {
            match st {
                Stmt::Assign { name, value } => {
                    let mut reads = Vec::new();
                    expr_reads(value, &mut reads);
                    for r in reads {
                        out.entry(r.clone()).or_insert(TOUCH_READ);
                    }
                    out.entry(name.clone()).or_insert(match top {
                        true => TOUCH_TOPWRITE,
                        false => TOUCH_NESTED_WRITE,
                    });
                }
                Stmt::ArrayAssign {
                    array,
                    index,
                    value,
                } => {
                    let mut reads = Vec::new();
                    expr_reads(index, &mut reads);
                    expr_reads(value, &mut reads);
                    for r in reads {
                        out.entry(r.clone()).or_insert(TOUCH_READ);
                    }
                    out.entry(array.clone()).or_insert(match top {
                        true => TOUCH_TOPWRITE,
                        false => TOUCH_NESTED_WRITE,
                    });
                }
                Stmt::Assert(e) => {
                    let mut reads = Vec::new();
                    expr_reads(e, &mut reads);
                    for r in reads {
                        out.entry(r.clone()).or_insert(TOUCH_READ);
                    }
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                } => {
                    let mut reads = Vec::new();
                    expr_reads(cond, &mut reads);
                    for r in reads {
                        out.entry(r.clone()).or_insert(TOUCH_READ);
                    }
                    scan(then_body, out, false);
                    scan(else_body, out, false);
                }
                Stmt::While { cond, body, .. } => {
                    let mut reads = Vec::new();
                    expr_reads(cond, &mut reads);
                    for r in reads {
                        out.entry(r.clone()).or_insert(TOUCH_READ);
                    }
                    scan(body, out, false);
                }
            }
        }
    }
    let mut out = std::collections::HashMap::new();
    scan(prog, &mut out, true);
    out
}

/// How many assignments to `name` occur ANYWHERE in the program — loop
/// bodies included. A first-touch-deferred variable written again inside a
/// loop needs `mut`, and counting only the top level would miss exactly the
/// common accumulator shape (`i := 0; while … { i := i + 1 }`).
fn writes_total(prog: &Program, name: &str) -> usize {
    fn go(prog: &[Stmt], name: &str, c: &mut usize) {
        for s in prog {
            match s {
                Stmt::Assign { name: n, .. } if n == name => *c += 1,
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    go(then_body, name, c);
                    go(else_body, name, c);
                }
                Stmt::While { body, .. } => go(body, name, c),
                _ => {}
            }
        }
    }
    let mut c = 0;
    go(prog, name, &mut c);
    c
}

fn emit_rust(spec: &Spec, prog: &Program, cert_digest: &str) -> String {
    let mut s = String::new();
    s.push_str(&format!(
        "//! `{}` — generated by probatum (the intent compiler).\n//!\n\
         //! VERIFIED: this implementation satisfies every `ensures` clause of the\n\
         //! spec below for all inputs satisfying `requires`, over the declared\n\
         //! bounded domains — proven by two independent complete engines\n\
         //! (exhaustive enumeration + BDD symbolic reasoning) in agreement.\n//!\n\
         //! verified-by-cert-sha256: {}\n//!\n\
         //! ```text\n",
        spec.name, cert_digest
    ));
    // Embed the spec as a doc comment for traceability.
    for line in emit_dsl(spec, prog, cert_digest).lines() {
        s.push_str(&format!("//! {}\n", line));
    }
    s.push_str("//! ```\n\n");

    // Signature.
    let params: Vec<String> = spec
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, rust_ty(&p.ty)))
        .collect();
    let ret = if spec.results.len() == 1 {
        rust_ty(&spec.results[0].ty)
    } else {
        format!(
            "({})",
            spec.results
                .iter()
                .map(|r| rust_ty(&r.ty))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    s.push_str(&format!("pub fn {}({}) -> {} {{\n", spec.name, params.join(", "), ret));

    // Runtime backstop guards (NOT the proof — the certificate is).
    for p in &spec.params {
        if let Type::Int(r) = &p.ty {
            s.push_str(&format!(
                "    assert!({p} >= {lo} && {p} <= {hi}, \"precondition violated: {p} must be in [{lo}, {hi}]\");\n",
                p = p.name, lo = r.lo, hi = r.hi
            ));
        }
    }
    for (i, c) in spec.requires.iter().enumerate() {
        s.push_str(&format!(
            "    assert!({}, \"requires #{} violated: {}\");\n",
            emit_expr(c, TargetLang::Rust),
            i + 1,
            c.to_string().replace('"', "'")
        ));
    }

    // declarations
    //
    // Two shapes, decided by what the program is:
    //
    // * **Straight-line** (assignments only): every result gets exactly one
    //   write and is never read before it, so results become declarations AT
    //   the assignment — `let x = rhs;`. A pre-declared `let mut x = 0;` whose
    //   initializer the first statement overwrites is a dead store, and rustc
    //   is right to flag it. Locals are deferred the same way when a
    //   first-touch scan proves the invariant value is never read first.
    //
    // * **Control flow**: writes can be skipped or redone mid-flight, and the
    //   machine's initial value (bottom of the declared domain) is part of
    //   the verified semantics — every variable is declared up front,
    //   initialized, and mutable.
    let touch = first_touch_scan(prog);
    let writes_of = |name: &str, prog: &Program| writes_total(prog, name);

    // Locals: the initial value survives only when some execution can read
    // it before any write (first touch = READ, or a write reachable only on
    // some runs). Arrays are never deferred — a write targets one element,
    // so the rest must exist.
    for l in &spec.locals {
        let touch = touch.get(&l.name);
        let defer = touch == Some(&TOUCH_TOPWRITE) && !matches!(l.ty, Type::Array { .. });
        match l.ty {
            Type::Array { index, elem } => s.push_str(&format!(
                "    let mut {}: Vec<i64> = vec![{}i64; {}];\n",
                l.name,
                elem.lo,
                index.size()
            )),
            Type::Int(r) if !defer => {
                let writes = writes_of(l.name.as_str(), prog);
                s.push_str(&format!(
                    "    let {mut_}{}: i64 = {};\n",
                    l.name,
                    r.lo,
                    mut_ = if writes > 1 { "mut " } else { "" }
                ))
            }
            Type::Int(_) => {
                let writes = writes_of(l.name.as_str(), prog);
                if writes > 1 {
                    s.push_str(&format!("    let mut {}: i64;\n", l.name))
                } else {
                    s.push_str(&format!("    let {}: i64;\n", l.name))
                }
            }
            Type::Decimal { stored, .. } if !defer => {
                let writes = writes_of(l.name.as_str(), prog);
                s.push_str(&format!(
                    "    let {mut_}{}: i64 = {};\n",
                    l.name,
                    stored.lo,
                    mut_ = if writes > 1 { "mut " } else { "" }
                ))
            }
            Type::Decimal { .. } => s.push_str(&format!("    let {}: i64;\n", l.name)),
            Type::Bool if !defer => {
                let writes = writes_of(l.name.as_str(), prog);
                s.push_str(&format!(
                    "    let {mut_}{}: bool = false;\n",
                    l.name,
                    mut_ = if writes > 1 { "mut " } else { "" }
                ))
            }
            Type::Bool => s.push_str(&format!("    let {}: bool;\n", l.name)),
        }
    }

    // Results follow the same rule. A deferred result with exactly one
    // write becomes the `let` at that write (via `let_for` below); with
    // several writes it gets a plain binding the writes mutate. Arrays are
    // always allocated up front.
    let mut let_for: Vec<String> = Vec::new();
    for r in &spec.results {
        let scalar = !matches!(r.ty, Type::Array { .. });
        let defer = scalar && touch.get(&r.name) == Some(&TOUCH_TOPWRITE);
        if defer && writes_of(r.name.as_str(), prog) == 1 {
            let_for.push(r.name.clone());
            continue;
        }
        if defer {
            match r.ty {
                Type::Int(_) => s.push_str(&format!("    let mut {}: i64;\n", r.name)),
                Type::Decimal { .. } => s.push_str(&format!("    let mut {}: i64;\n", r.name)),
                Type::Bool => s.push_str(&format!("    let mut {}: bool;\n", r.name)),
                Type::Array { .. } => {}
            }
            continue;
        }
        match r.ty {
            Type::Array { index, elem } => s.push_str(&format!(
                "    let mut {}: Vec<i64> = vec![{}i64; {}];\n",
                r.name,
                elem.lo,
                index.size()
            )),
            Type::Int(range) => {
                s.push_str(&format!("    let mut {}: i64 = {};\n", r.name, range.lo))
            }
            Type::Decimal { stored, .. } => {
                s.push_str(&format!("    let mut {}: i64 = {};\n", r.name, stored.lo))
            }
            Type::Bool => s.push_str(&format!("    let mut {}: bool = false;\n", r.name)),
        }
    }
    s.push_str(&emit_stmts(prog, TargetLang::Rust, 1, &let_for));

    // Postcondition backstops.
    for (i, c) in spec.ensures.iter().enumerate() {
        s.push_str(&format!(
            "    debug_assert!({}, \"ensures #{} violated: {}\");\n",
            emit_expr(c, TargetLang::Rust),
            i + 1,
            c.to_string().replace('"', "'")
        ));
    }

    // Return.
    if spec.results.len() == 1 {
        s.push_str(&format!("    {}\n", spec.results[0].name));
    } else {
        let names: Vec<String> = spec.results.iter().map(|r| r.name.clone()).collect();
        s.push_str(&format!("    ({})\n", names.join(", ")));
    }
    s.push_str("}\n");
    s
}

fn emit_go(spec: &Spec, prog: &Program, cert_digest: &str) -> String {
    let mut s = String::new();
    s.push_str(&format!(
        "// {} — generated by probatum (the intent compiler).\n//\n\
         // VERIFIED: satisfies every ensures clause for all inputs satisfying\n\
         // requires, over the declared bounded domains — proven by two\n\
         // independent complete engines in agreement.\n//\n\
         // verified-by-cert-sha256: {}\n\n",
        spec.name, cert_digest
    ));
    s.push_str("package verified\n\n");

    // Signature.
    let params: Vec<String> = spec
        .params
        .iter()
        .map(|p| format!("{} {}", p.name, go_ty(&p.ty)))
        .collect();
    let ret = if spec.results.len() == 1 {
        go_ty(&spec.results[0].ty)
    } else {
        format!(
            "({})",
            spec.results
                .iter()
                .map(|r| go_ty(&r.ty))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    s.push_str(&format!(
        "// {} is the verified implementation of the intent spec below.\n",
        spec.name
    ));
    for c in &spec.requires {
        s.push_str(&format!("//   requires {}\n", c));
    }
    for c in &spec.ensures {
        s.push_str(&format!("//   ensures  {}\n", c));
    }
    let go_name = capitalize(&spec.name);
    s.push_str(&format!("func {}({}) {} {{\n", go_name, params.join(", "), ret));

    for p in &spec.params {
        if let Type::Int(r) = &p.ty {
            s.push_str(&format!(
                "\tif {p} < {lo} || {p} > {hi} {{ panic(\"precondition violated: {p} must be in [{lo}, {hi}]\") }}\n",
                p = p.name, lo = r.lo, hi = r.hi
            ));
        }
    }
    for (i, c) in spec.requires.iter().enumerate() {
        s.push_str(&format!(
            "\tif !({}) {{ panic(\"requires #{} violated\") }}\n",
            emit_expr(c, TargetLang::Go),
            i + 1
        ));
    }
    for l in &spec.locals {
        match l.ty {
            Type::Array { index, elem } => s.push_str(&format!(
                "\t{} := make([]int64, {}); for i := range {} {{ {}[i] = {} }}\n",
                l.name,
                index.size(),
                l.name,
                l.name,
                elem.lo
            )),
            Type::Int(r) => s.push_str(&format!("\tvar {} int64 = {}\n", l.name, r.lo)),
            Type::Decimal { stored, .. } => {
                s.push_str(&format!("\tvar {} int64 = {}\n", l.name, stored.lo))
            }
            Type::Bool => s.push_str(&format!("\tvar {} bool = false\n", l.name)),
        }
    }
    for r in &spec.results {
        match r.ty {
            Type::Array { index, elem } => s.push_str(&format!(
                "\t{} := make([]int64, {}); for i := range {} {{ {}[i] = {} }}\n",
                r.name,
                index.size(),
                r.name,
                r.name,
                elem.lo
            )),
            Type::Int(range) => s.push_str(&format!("\tvar {} int64 = {}\n", r.name, range.lo)),
            Type::Decimal { stored, .. } => {
                s.push_str(&format!("\tvar {} int64 = {}\n", r.name, stored.lo))
            }
            Type::Bool => s.push_str(&format!("\tvar {} bool = false\n", r.name)),
        }
    }
    s.push_str(&emit_stmts(prog, TargetLang::Go, 0, &[]));
    for (i, c) in spec.ensures.iter().enumerate() {
        s.push_str(&format!(
            "\tif !({}) {{ panic(\"ensures #{} violated\") }}\n",
            emit_expr(c, TargetLang::Go),
            i + 1
        ));
    }
    if spec.results.len() == 1 {
        s.push_str(&format!("\treturn {}\n", spec.results[0].name));
    } else {
        let names: Vec<String> = spec.results.iter().map(|r| r.name.clone()).collect();
        s.push_str(&format!("\treturn {}\n", names.join(", ")));
    }
    s.push_str("}\n");
    s
}

fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
        None => String::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn transfer() -> (Spec, Program) {
        let s = parse(
            r#"
            spec transfer(a: int[0..255], b: int[0..255], amount: int[0..255])
              returns (x: int[0..255], y: int[0..255])
              requires amount <= a
              requires b + amount <= 255
              ensures x == a - amount
              ensures y == b + amount
              ensures x + y == a + b
            {
              x := a - amount;
              y := b + amount;
            }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let body = s.body.clone().unwrap();
        (s, body)
    }

    #[test]
    fn rust_output_contains_verified_marker_and_guards() {
        let (s, body) = transfer();
        let code = emit(&s, &body, TargetLang::Rust, "deadbeef").unwrap();
        assert!(code.contains("pub fn transfer"));
        assert!(code.contains("verified-by-cert-sha256: deadbeef"));
        // Precedence-aware emission: a comparison stands bare, and a
        // straight-line assignment declares its result AT the write — no
        // dead initializer for rustc to flag.
        assert!(code.contains("assert!(amount <= a"));
        assert!(code.contains("(x + y) == (a + b)"));
        assert!(code.contains("let x = a - amount;"));
        assert!(!code.contains("let mut x: i64 = 0;"));
    }

    #[test]
    fn rust_emission_groups_exactly_like_the_verified_tree() {
        // The emitter must parenthesize only what rustc's precedence would
        // otherwise group differently from the AST the prover verified.
        // Each case below is a grouping that changes the meaning if it is
        // dropped or mis-planned.

        // `a - b + a` == (a - b) + a: same tree, left child shares precedence.
        let add = Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Binary(
                BinOp::Sub,
                Box::new(Expr::Param("a".into())),
                Box::new(Expr::Param("b".into())),
            )),
            Box::new(Expr::Param("a".into())),
        );
        assert_eq!(
            rust_expr(&add, 0),
            "a - b + a",
            "left-associative chains stay bare"
        );

        // `a - (b + c)`: the right child of `-` at equal precedence NEEDS its
        // parens, or rustc would re-associate the subtraction.
        let wrong_group = Expr::Binary(
            BinOp::Sub,
            Box::new(Expr::Param("a".into())),
            Box::new(Expr::Binary(
                BinOp::Add,
                Box::new(Expr::Param("b".into())),
                Box::new(Expr::Param("c".into())),
            )),
        );
        assert_eq!(rust_expr(&wrong_group, 0), "a - (b + c)");

        // `&&` of comparisons: both sides stand bare (Rust groups tight ops
        // under loose ones automatically).
        let both = Expr::Binary(
            BinOp::And,
            Box::new(Expr::Binary(
                BinOp::Ge,
                Box::new(Expr::Param("r".into())),
                Box::new(Expr::Param("lo".into())),
            )),
            Box::new(Expr::Binary(
                BinOp::Le,
                Box::new(Expr::Param("r".into())),
                Box::new(Expr::Param("hi".into())),
            )),
        );
        assert_eq!(rust_expr(&both, 0), "r >= lo && r <= hi");

        // Neg(Min): method call binds tighter than unary minus, so the
        // intended `-(a.min(b))` renders correctly as `-a.min(b)`.
        let neg_min = Expr::Unary(
            UnOp::Neg,
            Box::new(Expr::Min(
                Box::new(Expr::Param("a".into())),
                Box::new(Expr::Param("b".into())),
            )),
        );
        assert_eq!(rust_expr(&neg_min, 0), "-a.min(b)");

        // Min with a non-postfix receiver: `(a - b).min(0)` — the receiver
        // group is load-bearing (`a - b.min(0)` would bind differently).
        let min_recv = Expr::Min(
            Box::new(Expr::Binary(
                BinOp::Sub,
                Box::new(Expr::Param("a".into())),
                Box::new(Expr::Param("b".into())),
            )),
            Box::new(Expr::IntLit(0)),
        );
        assert_eq!(rust_expr(&min_recv, 0), "(a - b).min(0)");

        // A negative literal as receiver: `(-1).min(y)` is NOT the same as
        // `-(1.min(y))`.
        let min_neg_lit = Expr::Min(
            Box::new(Expr::IntLit(-1)),
            Box::new(Expr::Param("y".into())),
        );
        assert_eq!(rust_expr(&min_neg_lit, 0), "(-1).min(y)");

        // `if` as an operand must be grouped: `x + if …` would otherwise be
        // ambiguous against block syntax.
        let ite_operand = Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Param("x".into())),
            Box::new(Expr::Ite(
                Box::new(Expr::Param("c".into())),
                Box::new(Expr::IntLit(1)),
                Box::new(Expr::IntLit(2)),
            )),
        );
        assert_eq!(rust_expr(&ite_operand, 0), "x + (if c { 1 } else { 2 })");
    }

    #[test]
    fn go_output_has_panics_and_camel_case() {
        let (s, body) = transfer();
        let code = emit(&s, &body, TargetLang::Go, "deadbeef").unwrap();
        assert!(code.contains("func Transfer("));
        assert!(code.contains("panic(\"requires #1 violated\")"));
        assert!(code.contains("int64"));
    }

    #[test]
    fn dsl_output_reparses() {
        let (s, body) = transfer();
        let code = emit(&s, &body, TargetLang::Dsl, "deadbeef").unwrap();
        // Strip the comment header; the rest must parse as a spec.
        let body_start = code.find("spec ").unwrap();
        let reparsed = parse(&code[body_start..]).expect("generated DSL must reparse");
        assert_eq!(reparsed.name, "transfer");
        assert_eq!(reparsed.body.as_ref().unwrap().len(), 2);
    }

    #[test]
    fn ite_emitted_lazily_in_rust() {
        let s = parse(
            r#"
            spec sd(a: int[0..15], b: int[0..15]) returns (r: int[0..15])
              requires b != 0
              ensures r == a / b
            { r := a / b; }
            "#,
        )
        .unwrap();
        crate::sema::analyze(&s).unwrap();
        let body = s.body.clone().unwrap();
        let code = emit(&s, &body, TargetLang::Rust, "x").unwrap();
        assert!(code.contains("assert!(b != 0") && code.contains("r = a / b;"));
    }
}
