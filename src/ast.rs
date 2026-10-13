//! Abstract syntax for the Intent language.
//!
//! A spec is *behavioral intent*: what must be true before (requires), what
//! must be true after (ensures / invariants), and concrete witnesses
//! (examples). A program is a straight-line body of assignments. The compiler
//! either verifies a given body or synthesizes one that satisfies the intent.

use std::fmt;

/// A bounded integer type `int[lo..hi]`.
///
/// Bounded domains are not a limitation — they are the point. A verifier can
/// only claim "proved" over a domain it can actually cover, and every real
/// system (currency amounts, array indices, ports, counters) is bounded.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct IntRange {
    pub lo: i64,
    pub hi: i64,
}

impl IntRange {
    pub fn new(lo: i64, hi: i64) -> Self {
        debug_assert!(lo <= hi, "int range lo must be <= hi");
        IntRange { lo, hi }
    }

    /// Number of representable values in the domain.
    pub fn size(&self) -> u128 {
        (self.hi as i128 - self.lo as i128 + 1) as u128
    }

    pub fn contains(&self, v: i64) -> bool {
        v >= self.lo && v <= self.hi
    }
}

impl fmt::Display for IntRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "int[{}..{}]", self.lo, self.hi)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Type {
    Int(IntRange),
    Bool,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int(r) => write!(f, "{}", r),
            Type::Bool => write!(f, "bool"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "&&",
            BinOp::Or => "||",
        };
        f.write_str(s)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum UnOp {
    Neg,
    Not,
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            UnOp::Neg => "-",
            UnOp::Not => "!",
        })
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Expr {
    IntLit(i64),
    BoolLit(bool),
    /// Reference to a parameter by name.
    Param(String),
    /// Reference to a result variable: `result.x`.
    Result(String),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// `if cond then a else b` — total conditional (lazy in evaluation).
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `min(a, b)` — so common in intent that it earns a node.
    Min(Box<Expr>, Box<Expr>),
    Max(Box<Expr>, Box<Expr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::IntLit(v) => write!(f, "{}", v),
            Expr::BoolLit(b) => write!(f, "{}", b),
            Expr::Param(n) => write!(f, "{}", n),
            Expr::Result(n) => write!(f, "result.{}", n),
            Expr::Unary(op, e) => write!(f, "({}{})", op, e),
            Expr::Binary(op, l, r) => write!(f, "({} {} {})", l, op, r),
            Expr::Ite(c, a, b) => write!(f, "(if {} then {} else {})", c, a, b),
            Expr::Min(a, b) => write!(f, "min({}, {})", a, b),
            Expr::Max(a, b) => write!(f, "max({}, {})", a, b),
        }
    }
}

/// A straight-line assignment: `name := expr;`.
#[derive(Clone, PartialEq, Debug)]
pub struct Assign {
    pub name: String,
    pub value: Expr,
}

impl fmt::Display for Assign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} := {};", self.name, self.value)
    }
}

/// A declared parameter or result.
#[derive(Clone, PartialEq, Debug)]
pub struct Binding {
    pub name: String,
    pub ty: Type,
}

/// A concrete input→output witness.
#[derive(Clone, PartialEq, Debug)]
pub struct Example {
    pub inputs: Vec<i64>,
    pub outputs: Vec<i64>,
}

/// A complete behavioral specification.
#[derive(Clone, Debug)]
pub struct Spec {
    pub name: String,
    pub params: Vec<Binding>,
    pub results: Vec<Binding>,
    /// Preconditions on the inputs. Inputs violating these are out of domain.
    pub requires: Vec<Expr>,
    /// Postconditions relating inputs to `result.*`.
    pub ensures: Vec<Expr>,
    /// Concrete witnesses the synthesized program must reproduce.
    pub examples: Vec<Example>,
    /// An optional hand-written body. `None` ⇒ synthesize.
    pub body: Option<Vec<Assign>>,
}

impl Spec {
    pub fn result_index(&self, name: &str) -> Option<usize> {
        self.results.iter().position(|b| b.name == name)
    }

    /// Total size of the input domain (product of parameter domain sizes).
    pub fn input_domain_size(&self) -> u128 {
        self.params
            .iter()
            .map(|b| match &b.ty {
                Type::Int(r) => r.size(),
                Type::Bool => 2,
            })
            .product()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_basics() {
        let r = IntRange::new(0, 255);
        assert_eq!(r.size(), 256);
        assert!(r.contains(0) && r.contains(255) && !r.contains(256));
        let neg = IntRange::new(-100, 100);
        assert_eq!(neg.size(), 201);
        assert!(neg.contains(-100) && neg.contains(100) && !neg.contains(101));
    }

    #[test]
    fn expr_display_is_parseable_shape() {
        let e = Expr::Binary(
            BinOp::Ge,
            Box::new(Expr::Param("a".into())),
            Box::new(Expr::IntLit(3)),
        );
        assert_eq!(e.to_string(), "(a >= 3)");
    }
}
