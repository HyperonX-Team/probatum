//! Hand-rolled lexer for the Intent language.

use std::fmt;

#[derive(Clone, PartialEq, Debug)]
pub enum Tok {
    // keywords
    Spec,
    Returns,
    Requires,
    Ensures,
    Invariant, // alias for ensures, reads better on loop-like contracts
    Locals,
    While,
    Decreases,
    Assert,
    Forall,
    Exists,
    Sum,
    In,
    Len,
    Example,
    If,
    Then,
    Else,
    Min,
    Max,
    True,
    False,
    Result,
    IntKw,
    Bool,
    // punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Semi,
    Dot,
    DotDot,
    ColonEq, // :=
    Arrow,   // =>
    // operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    AndAnd,
    OrOr,
    Bang,
    // literals
    Ident(String),
    Int(i64),
    Eof,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tok::Spec => write!(f, "spec"),
            Tok::Returns => write!(f, "returns"),
            Tok::Requires => write!(f, "requires"),
            Tok::Ensures => write!(f, "ensures"),
            Tok::Invariant => write!(f, "invariant"),
            Tok::Locals => write!(f, "locals"),
            Tok::While => write!(f, "while"),
            Tok::Decreases => write!(f, "decreases"),
            Tok::Assert => write!(f, "assert"),
            Tok::Forall => write!(f, "forall"),
            Tok::Exists => write!(f, "exists"),
            Tok::Sum => write!(f, "sum"),
            Tok::In => write!(f, "in"),
            Tok::Len => write!(f, "len"),
            Tok::Example => write!(f, "example"),
            Tok::If => write!(f, "if"),
            Tok::Then => write!(f, "then"),
            Tok::Else => write!(f, "else"),
            Tok::Min => write!(f, "min"),
            Tok::Max => write!(f, "max"),
            Tok::True => write!(f, "true"),
            Tok::False => write!(f, "false"),
            Tok::Result => write!(f, "result"),
            Tok::IntKw => write!(f, "int"),
            Tok::Bool => write!(f, "bool"),
            Tok::LParen => write!(f, "("),
            Tok::RParen => write!(f, ")"),
            Tok::LBrace => write!(f, "{{"),
            Tok::RBrace => write!(f, "}}"),
            Tok::LBracket => write!(f, "["),
            Tok::RBracket => write!(f, "]"),
            Tok::Comma => write!(f, ","),
            Tok::Colon => write!(f, ":"),
            Tok::Semi => write!(f, ";"),
            Tok::Dot => write!(f, "."),
            Tok::DotDot => write!(f, ".."),
            Tok::ColonEq => write!(f, ":="),
            Tok::Arrow => write!(f, "=>"),
            Tok::Plus => write!(f, "+"),
            Tok::Minus => write!(f, "-"),
            Tok::Star => write!(f, "*"),
            Tok::Slash => write!(f, "/"),
            Tok::Percent => write!(f, "%"),
            Tok::EqEq => write!(f, "=="),
            Tok::Ne => write!(f, "!="),
            Tok::Lt => write!(f, "<"),
            Tok::Le => write!(f, "<="),
            Tok::Gt => write!(f, ">"),
            Tok::Ge => write!(f, ">="),
            Tok::AndAnd => write!(f, "&&"),
            Tok::OrOr => write!(f, "||"),
            Tok::Bang => write!(f, "!"),
            Tok::Ident(s) => write!(f, "{}", s),
            Tok::Int(v) => write!(f, "{}", v),
            Tok::Eof => write!(f, "end of file"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Span {
    pub line: usize,
    pub col: usize,
}

#[derive(Clone, Debug)]
pub struct Spanned {
    pub tok: Tok,
    pub span: Span,
}

#[derive(Debug)]
pub struct LexError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.span.line, self.span.col, self.message)
    }
}

pub fn lex(src: &str) -> Result<Vec<Spanned>, LexError> {
    let mut out = Vec::new();
    let bytes = src.as_bytes();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut col = 1usize;

    macro_rules! bump {
        () => {{
            if bytes[i] == b'\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
            i += 1;
        }};
    }

    let span = |line: usize, col: usize| Span { line, col };

    while i < bytes.len() {
        let c = bytes[i];
        // whitespace
        if c == b' ' || c == b'\t' || c == b'\r' || c == b'\n' {
            bump!();
            continue;
        }
        // line comment
        if c == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                bump!();
            }
            continue;
        }
        // block comment /* ... */ (nesting allowed)
        if c == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            let start = span(line, col);
            bump!();
            bump!();
            let mut depth = 1usize;
            while i < bytes.len() && depth > 0 {
                if bytes[i] == b'*' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
                    bump!();
                    bump!();
                    depth -= 1;
                } else if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
                    bump!();
                    bump!();
                    depth += 1;
                } else {
                    bump!();
                }
            }
            if depth > 0 {
                return Err(LexError {
                    message: "unterminated block comment".into(),
                    span: start,
                });
            }
            continue;
        }

        let s = span(line, col);

        // identifiers / keywords
        if c.is_ascii_alphabetic() || c == b'_' {
            let mut name = String::new();
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                name.push(bytes[i] as char);
                bump!();
            }
            let tok = match name.as_str() {
                "spec" => Tok::Spec,
                "returns" => Tok::Returns,
                "requires" => Tok::Requires,
                "ensures" => Tok::Ensures,
                "invariant" => Tok::Invariant,
                "locals" => Tok::Locals,
                "while" => Tok::While,
                "decreases" => Tok::Decreases,
                "assert" => Tok::Assert,
                "forall" => Tok::Forall,
                "exists" => Tok::Exists,
                "sum" => Tok::Sum,
                "in" => Tok::In,
                "len" => Tok::Len,
                "example" => Tok::Example,
                "if" => Tok::If,
                "then" => Tok::Then,
                "else" => Tok::Else,
                "min" => Tok::Min,
                "max" => Tok::Max,
                "true" => Tok::True,
                "false" => Tok::False,
                "result" => Tok::Result,
                "int" => Tok::IntKw,
                "bool" => Tok::Bool,
                _ => Tok::Ident(name),
            };
            out.push(Spanned { tok, span: s });
            continue;
        }

        // numbers (including negative handled by unary minus)
        if c.is_ascii_digit() {
            let mut v: i64 = 0;
            let mut overflow = false;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                let d = (bytes[i] - b'0') as i64;
                v = v.saturating_mul(10).saturating_add(d);
                if v == i64::MAX {
                    overflow = true;
                }
                bump!();
            }
            if overflow {
                return Err(LexError {
                    message: "integer literal too large".into(),
                    span: s,
                });
            }
            out.push(Spanned {
                tok: Tok::Int(v),
                span: s,
            });
            continue;
        }

        // punctuation & operators (longest-match first)
        let two = if i + 1 < bytes.len() {
            Some((c, bytes[i + 1]))
        } else {
            None
        };
        let tok = match two {
            Some((b':', b'=')) => {
                bump!();
                bump!();
                Some(Tok::ColonEq)
            }
            Some((b'=', b'>')) => {
                bump!();
                bump!();
                Some(Tok::Arrow)
            }
            Some((b'=', b'=')) => {
                bump!();
                bump!();
                Some(Tok::EqEq)
            }
            Some((b'!', b'=')) => {
                bump!();
                bump!();
                Some(Tok::Ne)
            }
            Some((b'<', b'=')) => {
                bump!();
                bump!();
                Some(Tok::Le)
            }
            Some((b'>', b'=')) => {
                bump!();
                bump!();
                Some(Tok::Ge)
            }
            Some((b'&', b'&')) => {
                bump!();
                bump!();
                Some(Tok::AndAnd)
            }
            Some((b'|', b'|')) => {
                bump!();
                bump!();
                Some(Tok::OrOr)
            }
            Some((b'.', b'.')) => {
                bump!();
                bump!();
                Some(Tok::DotDot)
            }
            _ => None,
        };
        if let Some(tok) = tok {
            out.push(Spanned { tok, span: s });
            continue;
        }

        // single-char
        let tok = match c {
            b'(' => Some(Tok::LParen),
            b')' => Some(Tok::RParen),
            b'{' => Some(Tok::LBrace),
            b'}' => Some(Tok::RBrace),
            b'[' => Some(Tok::LBracket),
            b']' => Some(Tok::RBracket),
            b',' => Some(Tok::Comma),
            b':' => Some(Tok::Colon),
            b';' => Some(Tok::Semi),
            b'.' => Some(Tok::Dot),
            b'+' => Some(Tok::Plus),
            b'-' => Some(Tok::Minus),
            b'*' => Some(Tok::Star),
            b'/' => Some(Tok::Slash),
            b'%' => Some(Tok::Percent),
            b'<' => Some(Tok::Lt),
            b'>' => Some(Tok::Gt),
            b'!' => Some(Tok::Bang),
            _ => None,
        };
        if let Some(tok) = tok {
            bump!();
            out.push(Spanned { tok, span: s });
            continue;
        }

        return Err(LexError {
            message: format!("unexpected character {:?}", c as char),
            span: s,
        });
    }

    out.push(Spanned {
        tok: Tok::Eof,
        span: span(line, col),
    });
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexes_arrow_and_assign() {
        let toks = lex("x := a - 1; example (1) => (0)").unwrap();
        let kinds: Vec<&Tok> = toks.iter().map(|t| &t.tok).collect();
        assert!(kinds.iter().any(|t| matches!(t, Tok::ColonEq)));
        assert!(kinds.iter().any(|t| matches!(t, Tok::Arrow)));
    }

    #[test]
    fn comments_are_skipped() {
        let toks = lex("// hello\n/* block /* nested */ done */ spec").unwrap();
        assert!(matches!(toks[0].tok, Tok::Spec));
    }

    #[test]
    fn bad_char_reports_span() {
        let err = lex("spec @ x").unwrap_err();
        assert_eq!(err.span.line, 1);
        assert_eq!(err.span.col, 6);
    }
}
