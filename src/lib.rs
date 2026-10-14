//! probatum, as a library.
//!
//! The whole verifier is reachable from here: the parser, the reference
//! evaluator that defines the semantics, the two proof engines, the Hoare
//! condition generator and the code emitters. `src/main.rs` is a thin CLI over
//! exactly these modules, and so is the browser playground, which compiles
//! this library to WebAssembly and calls it through the C ABI in `wasm.rs`.
//!
//! Nothing here touches the filesystem, the environment or a subprocess — that
//! is deliberate, and it is what lets the same code run in a browser tab with
//! no shims.
pub mod ast;
pub mod bdd;
pub mod bitblast;
pub mod codegen;
pub mod eval;
pub mod hoare;
pub mod lexer;
pub mod parser;
pub mod prove;
pub mod sema;
pub mod sha256;
pub mod synth;

#[cfg(target_arch = "wasm32")]
pub mod wasm;