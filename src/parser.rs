//! Recursive-descent parser for the Intent language.
//!
//! Surface syntax:
//!
//! ```text
//! spec transfer(a: int[0..255], b: int[0..255], amount: int[0..255])
//!   returns (x: int[0..255], y: int[0..255])
//!   requires amount <= a
//!   requires b + amount <= 255
//!   ensures  x == a - amount
//!   ensures  y == b + amount
//!   ensures  x + y == a + b        // invariant: money is conserved
//!   example (100, 50, 25) => (75, 75)
//!   example (10, 10, 10)  => (0, 20)
//! {
//!   x := a - amount;
//!   y := b + amount;
//! }
//! ```
//!
//! The body is optional: omit it and the compiler synthesizes one.

use crate::ast::*;
use crate::lexer::{Span, Spanned, Tok};
use std::fmt;

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.span.line, self.span.col, self.message)
    }
}

pub struct Parser {
    toks: Vec<Spanned>,
    pos: usize,
}

type PResult<T> = Result<T, ParseError>;

impl Parser {
    pub fn new(toks: Vec<Spanned>) -> Self {
        Parser { toks, pos: 0 }
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn span(&self) -> Span {
        self.toks[self.pos].span.clone()
    }

    fn advance(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    fn at(&self, t: &Tok) -> bool {
        self.peek() == t
    }

    fn eat(&mut self, t: &Tok) -> PResult<bool> {
        if self.at(t) {
            self.advance();
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn expect(&mut self, t: &Tok, what: &str) -> PResult<()> {
        if self.at(t) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError {
                message: format!("expected {} but found `{}`", what, self.peek()),
                span: self.span(),
            })
        }
    }

    fn expect_ident(&mut self, what: &str) -> PResult<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.advance();
                Ok(s)
            }
            other => Err(ParseError {
                message: format!("expected {} but found `{}`", what, other),
                span: self.span(),
            }),
        }
    }

    // ---- grammar ----------------------------------------------------------

    pub fn parse_spec(&mut self) -> PResult<Spec> {
        self.expect(&Tok::Spec, "`spec`")?;
        let name = self.expect_ident("spec name")?;

        // params
        self.expect(&Tok::LParen, "`(`")?;
        let mut params = Vec::new();
        if !self.at(&Tok::RParen) {
            loop {
                params.push(self.parse_binding()?);
                if !self.eat(&Tok::Comma)? {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "`)`")?;

        // returns
        self.expect(&Tok::Returns, "`returns`")?;
        self.expect(&Tok::LParen, "`(`")?;
        let mut results = Vec::new();
        if !self.at(&Tok::RParen) {
            loop {
                results.push(self.parse_binding()?);
                if !self.eat(&Tok::Comma)? {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "`)`")?;

        // optional `locals ( i: int[0..100], acc: int[0..999] )`
        let mut locals = Vec::new();
        if self.at(&Tok::Locals) {
            self.advance();
            self.expect(&Tok::LParen, "`(`")?;
            if !self.at(&Tok::RParen) {
                loop {
                    locals.push(self.parse_binding()?);
                    if !self.eat(&Tok::Comma)? {
                        break;
                    }
                }
            }
            self.expect(&Tok::RParen, "`)`")?;
        }

        // clauses
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut examples = Vec::new();
        loop {
            match self.peek() {
                Tok::Requires => {
                    self.advance();
                    requires.push(self.parse_expr()?);
                }
                Tok::Ensures | Tok::Invariant => {
                    self.advance();
                    ensures.push(self.parse_expr()?);
                }
                Tok::Example => {
                    self.advance();
                    examples.push(self.parse_example(&params, &results)?);
                }
                Tok::LBrace | Tok::Eof => break,
                other => {
                    return Err(ParseError {
                        message: format!(
                            "expected `requires`, `ensures`, `example`, or `{{` but found `{}`",
                            other
                        ),
                        span: self.span(),
                    })
                }
            }
        }

        // optional body
        let body = if self.at(&Tok::LBrace) {
            self.expect(&Tok::LBrace, "`{`")?;
            let prog = self.parse_stmts()?;
            Some(prog)
        } else {
            None
        };

        self.expect(&Tok::Eof, "end of spec")?;

        Ok(Spec {
            name,
            params,
            results,
            locals,
            requires,
            ensures,
            examples,
            body,
        })
    }

    fn parse_binding(&mut self) -> PResult<Binding> {
        let name = self.expect_ident("parameter name")?;
        self.expect(&Tok::Colon, "`:`")?;
        let ty = self.parse_type()?;
        Ok(Binding { name, ty })
    }

    fn parse_type(&mut self) -> PResult<Type> {
        match self.peek().clone() {
            Tok::IntKw => {
                self.advance();
                self.expect(&Tok::LBracket, "`[`")?;
                let lo = self.parse_signed_int()?;
                self.expect(&Tok::DotDot, "`..`")?;
                let hi = self.parse_signed_int()?;
                self.expect(&Tok::RBracket, "`]`")?;
                if lo > hi {
                    return Err(ParseError {
                        message: format!("empty range int[{}..{}]", lo, hi),
                        span: self.span(),
                    });
                }
                Ok(Type::Int(IntRange::new(lo, hi)))
            }
            // `array[4] of int[0..9]` — the index domain is 0..3.
            Tok::ArrayKw => {
                self.advance();
                self.expect(&Tok::LBracket, "`[`")?;
                let n = self.parse_signed_int()?;
                self.expect(&Tok::RBracket, "`]`")?;
                if n <= 0 {
                    return Err(ParseError {
                        message: format!("array length must be positive, got {}", n),
                        span: self.span(),
                    });
                }
                self.expect(&Tok::Of, "`of`")?;
                let elem = self.parse_type()?;
                let elem_range = match elem {
                    Type::Int(r) => r,
                    Type::Decimal { stored, .. } => stored,
                    other => {
                        return Err(ParseError {
                            message: format!("array elements must be int, got `{}`", other),
                            span: self.span(),
                        })
                    }
                };
                Ok(Type::Array {
                    index: IntRange::new(0, n - 1),
                    elem: elem_range,
                })
            }
            // `dec<2>[0..10000]` — value = stored / 10^2, so 0.00 .. 100.00.
            Tok::Dec => {
                self.advance();
                self.expect(&Tok::Lt, "`<`")?;
                let scale = self.parse_signed_int()?;
                self.expect(&Tok::Gt, "`>`")?;
                if !(0..=9).contains(&scale) {
                    return Err(ParseError {
                        message: format!("decimal scale must be 0..9, got {}", scale),
                        span: self.span(),
                    });
                }
                self.expect(&Tok::LBracket, "`[`")?;
                let lo = self.parse_signed_int()?;
                self.expect(&Tok::DotDot, "`..`")?;
                let hi = self.parse_signed_int()?;
                self.expect(&Tok::RBracket, "`]`")?;
                if lo > hi {
                    return Err(ParseError {
                        message: format!("empty decimal range dec<{}>[{}..{}]", scale, lo, hi),
                        span: self.span(),
                    });
                }
                Ok(Type::Decimal {
                    scale: scale as u32,
                    stored: IntRange::new(lo, hi),
                })
            }
            Tok::Bool => {
                self.advance();
                Ok(Type::Bool)
            }
            other => Err(ParseError {
                message: format!(
                    "expected a type (`int[..]`, `array[N] of T`, `dec<S>[..]`, or `bool`) \
                     but found `{}`",
                    other
                ),
                span: self.span(),
            }),
        }
    }

    fn parse_signed_int(&mut self) -> PResult<i64> {
        let neg = self.eat(&Tok::Minus)?;
        match self.peek().clone() {
            Tok::Int(v) => {
                self.advance();
                Ok(if neg { -v } else { v })
            }
            other => Err(ParseError {
                message: format!("expected an integer literal but found `{}`", other),
                span: self.span(),
            }),
        }
    }

    fn parse_example(&mut self, params: &[Binding], results: &[Binding]) -> PResult<Example> {
        self.expect(&Tok::LParen, "`(`")?;
        let mut inputs = Vec::new();
        if !self.at(&Tok::RParen) {
            loop {
                inputs.push(self.parse_signed_int()?);
                if !self.eat(&Tok::Comma)? {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "`)`")?;
        self.expect(&Tok::Arrow, "`=>`")?;
        self.expect(&Tok::LParen, "`(`")?;
        let mut outputs = Vec::new();
        if !self.at(&Tok::RParen) {
            loop {
                outputs.push(self.parse_signed_int()?);
                if !self.eat(&Tok::Comma)? {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "`)`")?;

        if inputs.len() != params.len() {
            return Err(ParseError {
                message: format!(
                    "example has {} input(s) but spec declares {} parameter(s)",
                    inputs.len(),
                    params.len()
                ),
                span: self.span(),
            });
        }
        if outputs.len() != results.len() {
            return Err(ParseError {
                message: format!(
                    "example has {} output(s) but spec declares {} result(s)",
                    outputs.len(),
                    results.len()
                ),
                span: self.span(),
            });
        }
        // Domain-check the witness: an example outside the declared domain is a spec bug.
        for (i, (v, b)) in inputs.iter().zip(params.iter()).enumerate() {
            match b.ty {
                Type::Int(r) if !r.contains(*v) => {
                    return Err(ParseError {
                        message: format!(
                            "example input #{} = {} is outside declared domain {} of `{}`",
                            i, v, r, b.name
                        ),
                        span: self.span(),
                    })
                }
                _ => {}
            }
        }
        for (i, (v, b)) in outputs.iter().zip(results.iter()).enumerate() {
            match b.ty {
                Type::Int(r) if !r.contains(*v) => {
                    return Err(ParseError {
                        message: format!(
                            "example output #{} = {} is outside declared domain {} of `{}`",
                            i, v, r, b.name
                        ),
                        span: self.span(),
                    })
                }
                _ => {}
            }
        }

        Ok(Example { inputs, outputs })
    }

    /// Parse a block body: a sequence of statements up to the closing `}`.
    fn parse_block(&mut self) -> PResult<Vec<Stmt>> {
        self.expect(&Tok::LBrace, "`{`")?;
        self.parse_stmts()
    }

    /// Parse statements until `}` (consuming it).
    fn parse_stmts(&mut self) -> PResult<Vec<Stmt>> {
        let mut stmts = Vec::new();
        loop {
            if self.at(&Tok::RBrace) {
                self.advance();
                break;
            }
            if self.at(&Tok::Eof) {
                return Err(ParseError {
                    message: "unterminated body: missing `}`".into(),
                    span: self.span(),
                });
            }
            stmts.push(self.parse_stmt()?);
        }
        Ok(stmts)
    }

    fn parse_stmt(&mut self) -> PResult<Stmt> {
        match self.peek().clone() {
            // ---- if / else -------------------------------------------------
            Tok::If => {
                self.advance();
                let cond = self.parse_expr()?;
                let then_body = self.parse_block()?;
                let mut else_body = Vec::new();
                if self.at(&Tok::Else) {
                    self.advance();
                    if self.at(&Tok::If) {
                        // `else if` — desugar one level into a nested if.
                        else_body.push(self.parse_stmt()?);
                    } else {
                        else_body = self.parse_block()?;
                    }
                }
                Ok(Stmt::If {
                    cond,
                    then_body,
                    else_body,
                })
            }

            // ---- while with invariants -------------------------------------
            Tok::While => {
                self.advance();
                let cond = self.parse_expr()?;
                let mut invariants = Vec::new();
                let mut decreases = None;
                // `invariant E` / `decreases E` may repeat, in any order,
                // before the body block. At least one invariant is required —
                // an invariant-free loop cannot be verified, only run.
                loop {
                    if self.at(&Tok::Invariant) {
                        self.advance();
                        invariants.push(self.parse_expr()?);
                    } else if self.at(&Tok::Decreases) {
                        self.advance();
                        decreases = Some(self.parse_expr()?);
                    } else {
                        break;
                    }
                }
                if invariants.is_empty() {
                    return Err(ParseError {
                        message: "a `while` loop needs at least one `invariant` — \
                                  without one the loop cannot be verified, only run"
                            .into(),
                        span: self.span(),
                    });
                }
                let body = self.parse_block()?;
                Ok(Stmt::While {
                    cond,
                    invariants,
                    decreases,
                    body,
                })
            }

            // ---- assert ----------------------------------------------------
            Tok::Assert => {
                self.advance();
                let e = self.parse_expr()?;
                self.expect(&Tok::Semi, "`;`")?;
                Ok(Stmt::Assert(e))
            }

            // ---- assignment (scalar or indexed) ----------------------------
            Tok::Ident(name) => {
                self.advance();
                if self.at(&Tok::LBracket) {
                    // a[i] := e;
                    self.advance();
                    let index = self.parse_expr()?;
                    self.expect(&Tok::RBracket, "`]`")?;
                    self.expect(&Tok::ColonEq, "`:=`")?;
                    let value = self.parse_expr()?;
                    self.expect(&Tok::Semi, "`;`")?;
                    Ok(Stmt::ArrayAssign {
                        array: name,
                        index,
                        value,
                    })
                } else {
                    self.expect(&Tok::ColonEq, "`:=`")?;
                    let value = self.parse_expr()?;
                    self.expect(&Tok::Semi, "`;`")?;
                    Ok(Stmt::Assign { name, value })
                }
            }

            other => Err(ParseError {
                message: format!(
                    "expected a statement (assignment, `if`, `while`, `assert`) but found `{}`",
                    other
                ),
                span: self.span(),
            }),
        }
    }

    /// Every name assigned anywhere in the program (recursively).
    fn collect_assigned(prog: &[Stmt], out: &mut Vec<String>) {
        for s in prog {
            match s {
                Stmt::Assign { name, .. } => out.push(name.clone()),
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    Self::collect_assigned(then_body, out);
                    Self::collect_assigned(else_body, out);
                }
                Stmt::While { body, .. } => Self::collect_assigned(body, out),
                _ => {}
            }
        }
    }

    // Expression precedence: || < && < comparison < additive < multiplicative < unary < primary

    pub fn parse_expr(&mut self) -> PResult<Expr> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_and()?;
        while self.at(&Tok::OrOr) {
            self.advance();
            let rhs = self.parse_and()?;
            lhs = Expr::Binary(BinOp::Or, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_cmp()?;
        while self.at(&Tok::AndAnd) {
            self.advance();
            let rhs = self.parse_cmp()?;
            lhs = Expr::Binary(BinOp::And, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> PResult<Expr> {
        let lhs = self.parse_additive()?;
        let op = match self.peek() {
            Tok::EqEq => BinOp::Eq,
            Tok::Ne => BinOp::Ne,
            Tok::Lt => BinOp::Lt,
            Tok::Le => BinOp::Le,
            Tok::Gt => BinOp::Gt,
            Tok::Ge => BinOp::Ge,
            _ => return Ok(lhs),
        };
        self.advance();
        let rhs = self.parse_additive()?;
        Ok(Expr::Binary(op, Box::new(lhs), Box::new(rhs)))
    }

    fn parse_additive(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_multiplicative()?;
        loop {
            let op = match self.peek() {
                Tok::Plus => BinOp::Add,
                Tok::Minus => BinOp::Sub,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_multiplicative()?;
            lhs = Expr::Binary(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_multiplicative(&mut self) -> PResult<Expr> {
        let mut lhs = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                Tok::Star => BinOp::Mul,
                Tok::Slash => BinOp::Div,
                Tok::Percent => BinOp::Mod,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_unary()?;
            lhs = Expr::Binary(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> PResult<Expr> {
        if self.at(&Tok::Minus) {
            self.advance();
            let e = self.parse_unary()?;
            return Ok(Expr::Unary(UnOp::Neg, Box::new(e)));
        }
        if self.at(&Tok::Bang) {
            self.advance();
            let e = self.parse_unary()?;
            return Ok(Expr::Unary(UnOp::Not, Box::new(e)));
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> PResult<Expr> {
        match self.peek().clone() {
            Tok::Int(v) => {
                self.advance();
                Ok(Expr::IntLit(v))
            }
            Tok::True => {
                self.advance();
                Ok(Expr::BoolLit(true))
            }
            Tok::False => {
                self.advance();
                Ok(Expr::BoolLit(false))
            }
            Tok::If => {
                self.advance();
                let cond = self.parse_expr()?;
                self.expect(&Tok::Then, "`then`")?;
                let a = self.parse_expr()?;
                self.expect(&Tok::Else, "`else`")?;
                let b = self.parse_expr()?;
                Ok(Expr::Ite(Box::new(cond), Box::new(a), Box::new(b)))
            }
            Tok::Min => {
                self.advance();
                self.expect(&Tok::LParen, "`(`")?;
                let a = self.parse_expr()?;
                self.expect(&Tok::Comma, "`,`")?;
                let b = self.parse_expr()?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(Expr::Min(Box::new(a), Box::new(b)))
            }
            Tok::Max => {
                self.advance();
                self.expect(&Tok::LParen, "`(`")?;
                let a = self.parse_expr()?;
                self.expect(&Tok::Comma, "`,`")?;
                let b = self.parse_expr()?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(Expr::Max(Box::new(a), Box::new(b)))
            }
            Tok::Result => {
                self.advance();
                self.expect(&Tok::Dot, "`.`")?;
                let name = self.expect_ident("result variable")?;
                Ok(Expr::Result(name))
            }
            Tok::Ident(name) => {
                self.advance();
                // `a[i]` — indexed read.
                if self.at(&Tok::LBracket) {
                    self.advance();
                    let index = self.parse_expr()?;
                    self.expect(&Tok::RBracket, "`]`")?;
                    Ok(Expr::ArrayRead(name, Box::new(index)))
                } else {
                    Ok(Expr::Param(name))
                }
            }
            Tok::Len => {
                self.advance();
                self.expect(&Tok::LParen, "`(`")?;
                let name = self.expect_ident("array name")?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(Expr::Len(name))
            }
            Tok::Forall | Tok::Exists | Tok::Sum => {
                let kind = self.advance();
                // Two spellings:
                //   forall i in 0..n: BODY      (quantifier form)
                //   sum(i in 0..n: BODY)        (fold form, parenthesized)
                let parenthesized = self.eat(&Tok::LParen)?;
                let var = self.expect_ident("bound variable")?;
                self.expect(&Tok::In, "`in`")?;
                let lo = self.parse_additive()?;
                self.expect(&Tok::DotDot, "`..`")?;
                let hi = self.parse_additive()?;
                self.expect(&Tok::Colon, "`:`")?;
                let body = self.parse_expr()?;
                if parenthesized {
                    self.expect(&Tok::RParen, "`)`")?;
                }
                match kind {
                    Tok::Forall => Ok(Expr::Forall {
                        var,
                        lo: Box::new(lo),
                        hi: Box::new(hi),
                        body: Box::new(body),
                    }),
                    Tok::Exists => Ok(Expr::Exists {
                        var,
                        lo: Box::new(lo),
                        hi: Box::new(hi),
                        body: Box::new(body),
                    }),
                    _ => Ok(Expr::Sum {
                        var,
                        lo: Box::new(lo),
                        hi: Box::new(hi),
                        body: Box::new(body),
                    }),
                }
            }
            Tok::LParen => {
                self.advance();
                let e = self.parse_expr()?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(e)
            }
            other => Err(ParseError {
                message: format!("expected an expression but found `{}`", other),
                span: self.span(),
            }),
        }
    }
}

/// Lex + parse in one shot.
pub fn parse(src: &str) -> Result<Spec, String> {
    let toks = crate::lexer::lex(src).map_err(|e| e.to_string())?;
    let mut p = Parser::new(toks);
    p.parse_spec().map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec_src() -> String {
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
        "#
        .into()
    }

    #[test]
    fn parses_full_spec() {
        let s = parse(&spec_src()).expect("should parse");
        assert_eq!(s.name, "transfer");
        assert_eq!(s.params.len(), 3);
        assert_eq!(s.results.len(), 2);
        assert_eq!(s.requires.len(), 2);
        assert_eq!(s.ensures.len(), 3);
        assert_eq!(s.examples.len(), 1);
        let body = s.body.expect("body present");
        assert_eq!(body.len(), 2);
        match &body[0] {
            Stmt::Assign { name, .. } => assert_eq!(name, "x"),
            other => panic!("expected an assignment, got {:?}", other),
        }
    }

    #[test]
    fn body_optional() {
        let src = r#"
        spec noop(a: int[0..9])
          returns (r: int[0..9])
          ensures r == a
        "#;
        let s = parse(src).unwrap();
        assert!(s.body.is_none());
    }

    #[test]
    fn rejects_undeclared_assignment() {
        // Shape is now checked by semantic analysis (the parser just builds
        // the AST), so the diagnostic comes from `analyze`.
        let src = r#"
        spec s(a: int[0..9]) returns (r: int[0..9])
          ensures r == a
        { q := a; }
        "#;
        let s = parse(src).unwrap();
        let err = crate::sema::analyze(&s).unwrap_err();
        assert!(
            err.message.contains("undeclared variable"),
            "got: {}",
            err.message
        );
    }

    #[test]
    fn rejects_missing_assignment() {
        let src = r#"
        spec s(a: int[0..9]) returns (r: int[0..9], t: int[0..9])
          ensures r == a
        { r := a; }
        "#;
        let s = parse(src).unwrap();
        let err = crate::sema::analyze(&s).unwrap_err();
        assert!(err.message.contains("never assigned"), "got: {}", err.message);
    }

    #[test]
    fn rejects_out_of_domain_example() {
        let src = r#"
        spec s(a: int[0..9]) returns (r: int[0..9])
          ensures r == a
          example (42) => (42)
        "#;
        let err = parse(src).unwrap_err();
        assert!(err.contains("outside declared domain"), "got: {}", err);
    }

    #[test]
    fn negative_range_parses() {
        let s = parse("spec s(a: int[-100..100]) returns (r: int[-100..100]) ensures r == a").unwrap();
        match s.params[0].ty {
            Type::Int(r) => {
                assert_eq!(r.lo, -100);
                assert_eq!(r.hi, 100);
            }
            _ => panic!("expected int"),
        }
    }

    #[test]
    fn ite_min_max_parse() {
        let src = r#"
        spec s(a: int[0..9], b: int[0..9]) returns (r: int[0..9])
          ensures r == if a > b then max(a, b) else min(a, b)
        "#;
        let s = parse(src).unwrap();
        assert_eq!(s.ensures.len(), 1);
    }
}
