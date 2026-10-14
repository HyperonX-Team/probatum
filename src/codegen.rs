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
        _ => emit_expr_rust_like(e), // Rust and DSL share the shape
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
        // ---- arrays, quantifiers, folds -----------------------------------
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
        // ---- arrays, quantifiers, folds -----------------------------------
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
fn emit_stmts(stmts: &[Stmt], lang: TargetLang, indent: usize) -> String {
    let pad = "    ".repeat(indent);
    let mut s = String::new();
    for st in stmts {
        match st {
            Stmt::Assign { name, value } => {
                s.push_str(&format!("{}{} = {};\n", pad, name, emit_expr(value, lang)));
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
                s.push_str(&emit_stmts(then_body, lang, indent + 1));
                if else_body.is_empty() {
                    s.push_str(&format!("{}}}\n", pad));
                } else {
                    s.push_str(&format!("{}}} else {{\n", pad));
                    s.push_str(&emit_stmts(else_body, lang, indent + 1));
                    s.push_str(&format!("{}}}\n", pad));
                }
            }
            Stmt::While { cond, body, .. } => {
                s.push_str(&format!("{}while {} {{\n", pad, emit_expr(cond, lang)));
                s.push_str(&emit_stmts(body, lang, indent + 1));
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

    // Body: locals first (so the verifier's layout matches the emitted code),
    // then the verified program.
    for l in &spec.locals {
        match l.ty {
            Type::Array { index, elem } => s.push_str(&format!(
                "    let mut {}: Vec<i64> = vec![{}i64; {}];\n",
                l.name,
                elem.lo,
                index.size()
            )),
            Type::Int(r) => s.push_str(&format!("    let mut {}: i64 = {};\n", l.name, r.lo)),
            Type::Decimal { stored, .. } => {
                s.push_str(&format!("    let mut {}: i64 = {};\n", l.name, stored.lo))
            }
            Type::Bool => s.push_str(&format!("    let mut {}: bool = false;\n", l.name)),
        }
    }
    // Results are declared up front too: a result assigned only inside a
    // branch must still be definitely assigned on every path for the emitted
    // code to compile — and the verifier's job is to ensure it always is.
    for r in &spec.results {
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
    s.push_str(&emit_stmts(prog, TargetLang::Rust, 1));

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
    s.push_str(&emit_stmts(prog, TargetLang::Go, 0));
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
        assert!(code.contains("assert!((amount <= a)"));
        assert!(code.contains("((x + y) == (a + b))"));
        assert!(code.contains("(a - amount)"));
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
        assert!(code.contains("(a / b)"));
    }
}
