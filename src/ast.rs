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
    /// Fixed-size array / list: `arr[N] of int[lo..hi]`.
    ///
    /// The index domain is explicit (`int[0..N-1]`), and out-of-range
    /// indexing is a **fault** — the classic buffer-overflow bug becomes a
    /// proof obligation instead of a CVE. Strings are arrays of character
    /// codes; lists are arrays. Same machinery, different intent.
    Array {
        index: IntRange,
        elem: IntRange,
    },
    /// Exact fixed-point decimal: the true value is `stored / 10^scale`.
    ///
    /// This is how money actually works (cents), and unlike binary floating
    /// point it is **exact**: every value is a rational with denominator
    /// 10^scale, so arithmetic is precise and the prover can reason about it
    /// without an IEEE-754 model. `dec<2>` is "two decimal places".
    Decimal {
        scale: u32,
        /// Range of the *stored* integer (i.e. value × 10^scale).
        stored: IntRange,
    },
}

impl Type {
    /// The underlying integer domain of a scalar type (for proof engines).
    pub fn as_int_range(&self) -> Option<IntRange> {
        match self {
            Type::Int(r) => Some(*r),
            Type::Decimal { stored, .. } => Some(*stored),
            Type::Bool => Some(IntRange::new(0, 1)),
            Type::Array { .. } => None,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int(r) => write!(f, "{}", r),
            Type::Bool => write!(f, "bool"),
            Type::Array { index, elem } => {
                write!(f, "array[{}] of {}", index.size(), elem)
            }
            Type::Decimal { scale, stored } => {
                write!(f, "dec<{}>[{}]", scale, stored)
            }
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
    /// `a[i]` — indexed read from a fixed-size array. Out-of-range indices
    /// are a **fault** (violation), never a silent default.
    ArrayRead(String, Box<Expr>),
    /// `len(a)` — the fixed length of an array (a constant, but written as an
    /// expression so intent reads naturally).
    Len(String),
    /// `forall i in LO..HI: BODY` — universally quantified.
    Forall {
        var: String,
        lo: Box<Expr>,
        hi: Box<Expr>,
        body: Box<Expr>,
    },
    /// `exists i in LO..HI: BODY` — existentially quantified.
    Exists {
        var: String,
        lo: Box<Expr>,
        hi: Box<Expr>,
        body: Box<Expr>,
    },
    /// `sum(i in LO..HI: BODY)` — a fold, the workhorse of array intent.
    Sum {
        var: String,
        lo: Box<Expr>,
        hi: Box<Expr>,
        body: Box<Expr>,
    },
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
            Expr::ArrayRead(n, i) => write!(f, "{}[{}]", n, i),
            Expr::Len(n) => write!(f, "len({})", n),
            Expr::Forall { var, lo, hi, body } => {
                write!(f, "forall {} in {}..{}: {}", var, lo, hi, body)
            }
            Expr::Exists { var, lo, hi, body } => {
                write!(f, "exists {} in {}..{}: {}", var, lo, hi, body)
            }
            Expr::Sum { var, lo, hi, body } => {
                write!(f, "sum({} in {}..{}: {})", var, lo, hi, body)
            }
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

// ---------------------------------------------------------------------------
// Statements — the program language
// ---------------------------------------------------------------------------

/// A statement in a verified program.
///
/// Straight-line assignments are the base case; `if` and `while` add control
/// flow. A `while` loop carries its own **inductive invariant** — that is the
/// intent for the loop, and it is what makes the loop *provable* rather than
/// merely testable. Without an invariant a loop cannot be verified, only run.
#[derive(Clone, PartialEq, Debug)]
pub enum Stmt {
    /// `x := e;`
    Assign { name: String, value: Expr },
    /// `a[i] := e;` — indexed write into a fixed-size array.
    ArrayAssign {
        array: String,
        index: Expr,
        value: Expr,
    },
    /// `if cond { .. } else { .. }` — `else` may be empty.
    If {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    /// `while cond invariant I { .. }`
    ///
    /// Verified by Hoare logic: the invariant must hold on entry, be
    /// preserved by every iteration, and imply the postcondition together
    /// with the negated guard. `decreases` (optional) additionally proves
    /// termination by requiring a non-negative expression that strictly
    /// decreases on every iteration.
    While {
        cond: Expr,
        invariants: Vec<Expr>,
        decreases: Option<Expr>,
        body: Vec<Stmt>,
    },
    /// `assert E;` — an inline proof obligation, checked at that point.
    Assert(Expr),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Assign { name, value } => write!(f, "{} := {};", name, value),
            Stmt::ArrayAssign {
                array,
                index,
                value,
            } => write!(f, "{}[{}] := {};", array, index, value),
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                write!(f, "if {} {{", cond)?;
                for s in then_body {
                    write!(f, " {}", s)?;
                }
                if else_body.is_empty() {
                    write!(f, " }}")
                } else {
                    write!(f, " }} else {{")?;
                    for s in else_body {
                        write!(f, " {}", s)?;
                    }
                    write!(f, " }}")
                }
            }
            Stmt::While {
                cond,
                invariants,
                decreases,
                body,
            } => {
                write!(f, "while {} ", cond)?;
                for inv in invariants {
                    write!(f, "invariant {} ", inv)?;
                }
                if let Some(d) = decreases {
                    write!(f, "decreases {} ", d)?;
                }
                write!(f, "{{")?;
                for s in body {
                    write!(f, " {}", s)?;
                }
                write!(f, " }}")
            }
            Stmt::Assert(e) => write!(f, "assert {};", e),
        }
    }
}

/// A verified program: a sequence of statements.
pub type Program = Vec<Stmt>;

/// Render a program in canonical, re-parseable form (for certificates and
/// generated artifacts — the digest must be stable).
pub fn render_program_stmts(prog: &Program, indent: usize) -> String {
    let pad = "  ".repeat(indent);
    let mut out = String::new();
    for s in prog {
        match s {
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                out.push_str(&format!("{}if {} {{\n", pad, cond));
                out.push_str(&render_program_stmts(then_body, indent + 1));
                if else_body.is_empty() {
                    out.push_str(&format!("{}}}\n", pad));
                } else {
                    out.push_str(&format!("{}}} else {{\n", pad));
                    out.push_str(&render_program_stmts(else_body, indent + 1));
                    out.push_str(&format!("{}}}\n", pad));
                }
            }
            Stmt::While {
                cond,
                invariants,
                decreases,
                body,
            } => {
                out.push_str(&format!("{}while {} ", pad, cond));
                for inv in invariants {
                    out.push_str(&format!("invariant {} ", inv));
                }
                if let Some(d) = decreases {
                    out.push_str(&format!("decreases {} ", d));
                }
                out.push_str("{\n");
                out.push_str(&render_program_stmts(body, indent + 1));
                out.push_str(&format!("{}}}\n", pad));
            }
            other => out.push_str(&format!("{}{}\n", pad, other)),
        }
    }
    out
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
    /// Local variables (loop counters, accumulators). Statically typed so the
    /// verifier always knows every variable's exact domain — no inference, no
    /// guessing. Verified in Hoare-logic obligations, not exposed to callers.
    pub locals: Vec<Binding>,
    /// Preconditions on the inputs. Inputs violating these are out of domain.
    pub requires: Vec<Expr>,
    /// Postconditions relating inputs to `result.*`.
    pub ensures: Vec<Expr>,
    /// Concrete witnesses the synthesized program must reproduce.
    pub examples: Vec<Example>,
    /// An optional hand-written body. `None` ⇒ synthesize.
    pub body: Option<Program>,
}

impl Spec {
    pub fn result_index(&self, name: &str) -> Option<usize> {
        self.results.iter().position(|b| b.name == name)
    }

    /// Every variable in scope inside a body: parameters, then locals, then
    /// results. This ordering is the canonical layout used by proof engines.
    pub fn all_vars(&self) -> Vec<Binding> {
        let mut v: Vec<Binding> = self.params.clone();
        v.extend(self.locals.iter().cloned());
        v.extend(self.results.iter().cloned());
        v
    }

    /// Total size of the input domain (product of parameter domain sizes).
    ///
    /// Arrays contribute the product of their element domains — an array of
    /// 4 elements each in [0..9] has 10^4 = 10,000 possible contents, and
    /// that is exactly what an exhaustive engine must enumerate.
    pub fn input_domain_size(&self) -> u128 {
        self.params.iter().map(binding_domain_size).product()
    }
}

/// Number of distinct values a binding can take.
pub fn binding_domain_size(b: &Binding) -> u128 {
    match &b.ty {
        Type::Int(r) => r.size(),
        Type::Decimal { stored, .. } => stored.size(),
        Type::Bool => 2,
        Type::Array { elem, .. } => elem.size(),
    }
}

/// The flat list of scalar domains the parameters induce, in input order.
///
/// An array parameter of `N` elements contributes `N` domains — which is
/// exactly right for enumeration: an exhaustive engine must try every array
/// *content*, and that product is what this describes.
pub fn input_domains(spec: &Spec) -> Vec<IntRange> {
    let mut out = Vec::new();
    for b in &spec.params {
        match b.ty {
            Type::Array { index, elem } => {
                for _ in 0..index.size() {
                    out.push(elem);
                }
            }
            Type::Int(r) => out.push(r),
            Type::Decimal { stored, .. } => out.push(stored),
            Type::Bool => out.push(IntRange::new(0, 1)),
        }
    }
    out
}

/// Extract a straight-line program as the legacy `Vec<Assign>` form.
///
/// Returns `None` when the program has control flow or arrays — those go
/// through Hoare-logic obligations instead. This is the compatibility layer
/// that keeps the original (fast, cross-validated) proof path for the
/// straight-line subset while control flow gets its own treatment.
pub fn as_straight_line(prog: &Program) -> Option<Vec<Assign>> {
    let mut out = Vec::new();
    for s in prog {
        match s {
            Stmt::Assign { name, value } => out.push(Assign {
                name: name.clone(),
                value: value.clone(),
            }),
            _ => return None,
        }
    }
    Some(out)
}

/// Wrap a straight-line assignment list as a statement program.
pub fn assigns_to_program(body: &[Assign]) -> Program {
    body.iter()
        .map(|a| Stmt::Assign {
            name: a.name.clone(),
            value: a.value.clone(),
        })
        .collect()
}

/// Does this statement touch array state? (Engines need to know whether the
/// program state includes arrays, which changes the symbolic encoding.)
pub fn program_uses_arrays(prog: &Program) -> bool {
    prog.iter().any(|s| match s {
        Stmt::ArrayAssign { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => program_uses_arrays(then_body) || program_uses_arrays(else_body),
        Stmt::While { body, .. } => program_uses_arrays(body),
        _ => false,
    })
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
