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
            Some(self.parse_body(&results)?)
        } else {
            None
        };

        self.expect(&Tok::Eof, "end of spec")?;

        Ok(Spec {
            name,
            params,
            results,
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
            Tok::Bool => {
                self.advance();
                Ok(Type::Bool)
            }
            other => Err(ParseError {
                message: format!("expected a type (`int[..]` or `bool`) but found `{}`", other),
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

    fn parse_body(&mut self, results: &[Binding]) -> PResult<Vec<Assign>> {
        self.expect(&Tok::LBrace, "`{`")?;
        let mut assigns = Vec::new();
        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(ParseError {
                    message: "unterminated body: missing `}`".into(),
                    span: self.span(),
                });
            }
            let name = self.expect_ident("assignment target")?;
            if !results.iter().any(|b| b.name == name) {
                return Err(ParseError {
                    message: format!(
                        "`{}` is not a declared result variable (assignments target results)",
                        name
                    ),
                    span: self.span(),
                });
            }
            if assigns.iter().any(|a: &Assign| a.name == name) {
                return Err(ParseError {
                    message: format!("duplicate assignment to result `{}`", name),
                    span: self.span(),
                });
            }
            self.expect(&Tok::ColonEq, "`:=`")?;
            let value = self.parse_expr()?;
            self.expect(&Tok::Semi, "`;`")?;
            assigns.push(Assign { name, value });
        }
        self.expect(&Tok::RBrace, "`}`")?;

        // Every result must be assigned exactly once.
        for b in results {
            if !assigns.iter().any(|a| a.name == b.name) {
                return Err(ParseError {
                    message: format!("result `{}` is never assigned in the body", b.name),
                    span: self.span(),
                });
            }
        }
        Ok(assigns)
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
                Ok(Expr::Param(name))
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
        assert_eq!(body[0].name, "x");
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
        let src = r#"
        spec s(a: int[0..9]) returns (r: int[0..9])
          ensures r == a
        { q := a; }
        "#;
        let err = parse(src).unwrap_err();
        assert!(err.contains("not a declared result"), "got: {}", err);
    }

    #[test]
    fn rejects_missing_assignment() {
        let src = r#"
        spec s(a: int[0..9]) returns (r: int[0..9], t: int[0..9])
          ensures r == a
        { r := a; }
        "#;
        let err = parse(src).unwrap_err();
        assert!(err.contains("never assigned"), "got: {}", err);
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
