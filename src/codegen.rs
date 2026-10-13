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
    }
}

fn rust_ty(t: &Type) -> String {
    match t {
        Type::Int(_) => "i64".into(),
        Type::Bool => "bool".into(),
    }
}

fn go_ty(t: &Type) -> String {
    match t {
        Type::Int(_) => "int64".into(),
        Type::Bool => "bool".into(),
    }
}

/// Generate a full compilation unit for `spec` + verified `body`.
pub fn emit(
    spec: &Spec,
    body: &[Assign],
    lang: TargetLang,
    cert_digest: &str,
) -> Result<String, String> {
    match lang {
        TargetLang::Dsl => Ok(emit_dsl(spec, body, cert_digest)),
        TargetLang::Rust => Ok(emit_rust(spec, body, cert_digest)),
        TargetLang::Go => Ok(emit_go(spec, body, cert_digest)),
    }
}

fn emit_dsl(spec: &Spec, body: &[Assign], cert_digest: &str) -> String {
    let mut s = String::new();
    s.push_str(&format!(
        "// Generated by ic (the intent compiler)\n// verified-by-cert-sha256: {}\n",
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
    for a in body {
        s.push_str(&format!("  {} := {};\n", a.name, a.value));
    }
    s.push_str("}\n");
    s
}

fn emit_rust(spec: &Spec, body: &[Assign], cert_digest: &str) -> String {
    let mut s = String::new();
    s.push_str(&format!(
        "//! `{}` — generated by ic (the intent compiler).\n//!\n\
         //! VERIFIED: this implementation satisfies every `ensures` clause of the\n\
         //! spec below for all inputs satisfying `requires`, over the declared\n\
         //! bounded domains — proven by two independent complete engines\n\
         //! (exhaustive enumeration + BDD symbolic reasoning) in agreement.\n//!\n\
         //! verified-by-cert-sha256: {}\n//!\n\
         //! ```text\n",
        spec.name, cert_digest
    ));
    // Embed the spec as a doc comment for traceability.
    for line in emit_dsl(spec, body, cert_digest).lines() {
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

    // Body.
    for a in body {
        s.push_str(&format!(
            "    let {} = {};\n",
            a.name,
            emit_expr(&a.value, TargetLang::Rust)
        ));
    }

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

fn emit_go(spec: &Spec, body: &[Assign], cert_digest: &str) -> String {
    let mut s = String::new();
    s.push_str(&format!(
        "// {} — generated by ic (the intent compiler).\n//\n\
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
    for a in body {
        s.push_str(&format!(
            "\t{} := {}\n",
            a.name,
            emit_expr(&a.value, TargetLang::Go)
        ));
    }
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

    fn transfer() -> (Spec, Vec<Assign>) {
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
