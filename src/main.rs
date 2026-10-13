//! `ic` — The Intent Compiler.
//!
//! You write *behavioral intent* (preconditions, postconditions, invariants,
//! witnesses). `ic` verifies a program against that intent — or synthesizes
//! one — and emits a machine-checkable proof certificate that a separate,
//! independent verification path can re-derive from scratch.

mod ast;
mod bdd;
mod bitblast;
mod eval;
mod lexer;
mod parser;
mod prove;
mod sema;
mod sha256;
mod synth;

fn main() {
    println!("ic — the intent compiler");
}
