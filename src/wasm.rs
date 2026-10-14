//! The C ABI the browser playground talks to.
//!
//! WebAssembly in the browser, with **no wasm-bindgen and no dependencies** —
//! the same rule the rest of this crate follows, applied to the browser build.
//! Strings cross the boundary through linear memory: JavaScript allocates a
//! buffer with `probatum_alloc`, writes the spec into it, calls
//! `probatum_prove`, and reads a JSON result back from `probatum_result_ptr`.
//!
//! This module exists only for `wasm32`. Everything it calls is the same code
//! the CLI calls, so a verdict in the browser is produced by the same two
//! engines that produce a certificate on the command line — not by a
//! reimplementation that might drift.

use crate::prove::{ProverOptions, Verdict};
use std::sync::atomic::{AtomicUsize, Ordering};

/// Where the most recent JSON result begins. Stored as an address because a
/// `static mut` would need unsafe code for no benefit; this is single-threaded
/// wasm, so a relaxed atomic is exact.
static RESULT_PTR: AtomicUsize = AtomicUsize::new(0);

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn json_string(s: &str) -> String {
    format!("\"{}\"", escape(s))
}

fn json_strings(items: &[String]) -> String {
    let parts: Vec<String> = items.iter().map(|s| json_string(s)).collect();
    format!("[{}]", parts.join(","))
}

/// The verdict as a word, without the engine's internal formatting.
fn verdict_word(v: &Verdict) -> String {
    match v {
        Verdict::Proved => "PROVED".into(),
        Verdict::Violated => "VIOLATED".into(),
        Verdict::NoViolationFound => "NO VIOLATION FOUND".into(),
        Verdict::GaveUp { reason } => format!("GAVE UP: {}", reason),
    }
}

/// Run the whole verifier over a spec source and return a JSON report.
///
/// Errors are reported as data, never as a panic: a playground that shows a
/// blank page on a typo teaches nothing.
pub fn check_source(src: &str) -> String {
    let spec = match crate::parser::parse(src) {
        Ok(s) => s,
        Err(e) => {
            return format!(
                "{{\"ok\":false,\"stage\":\"parse\",\"message\":{}}}",
                json_string(&e.to_string())
            )
        }
    };
    if let Err(e) = crate::sema::analyze(&spec) {
        return format!(
            "{{\"ok\":false,\"stage\":\"check\",\"message\":{}}}",
            json_string(&e.to_string())
        );
    }
    let prog = match &spec.body {
        Some(p) => p.clone(),
        None => {
            return format!(
                "{{\"ok\":false,\"stage\":\"body\",\"message\":{}}}",
                json_string(
                    "this spec declares intent but no body — add `{ ... }` and probatum \
                     will prove it, or check it for internal consistency with `requires`/`ensures`"
                )
            )
        }
    };

    let result = crate::prove::prove(&spec, &prog, &ProverOptions::default());

    let engines: Vec<String> = result
        .engines
        .iter()
        .map(|e| {
            format!(
                "{{\"name\":{},\"verdict\":{},\"checked\":{},\"nodes\":{},\"notes\":{}}}",
                json_string(&e.engine),
                json_string(&verdict_word(&e.verdict)),
                e.checked,
                e.nodes.map(|n| n.to_string()).unwrap_or_else(|| "null".into()),
                json_strings(&e.notes)
            )
        })
        .collect();

    let (inputs, cause) = match &result.counterexample {
        Some(cx) => {
            let pairs: Vec<String> = cx
                .inputs
                .iter()
                .map(|(k, v)| format!("{}={}", k, v))
                .collect();
            (json_string(&pairs.join(", ")), json_string(&cx.violation))
        }
        None => ("null".into(), "null".into()),
    };

    format!(
        "{{\"ok\":true,\"verdict\":{},\"engines\":[{}],\"input\":{},\"cause\":{},\
          \"suggestions\":{},\"crossValidated\":{},\"domain\":{}}}",
        json_string(&verdict_word(&result.verdict)),
        engines.join(","),
        inputs,
        cause,
        json_strings(&result.suggestions),
        result.cross_validated,
        spec.input_domain_size()
    )
}

/// Allocate `len` bytes the caller will write into.
#[no_mangle]
pub extern "C" fn probatum_alloc(len: usize) -> *mut u8 {
    let mut v: Vec<u8> = Vec::with_capacity(len.max(1));
    let p = v.as_mut_ptr();
    std::mem::forget(v); // handed to the caller; reclaimed by the wasm instance
    p
}

/// Verify a spec whose bytes are at `ptr`. Returns the length of the JSON
/// result, which the caller reads from `probatum_result_ptr`.
#[no_mangle]
pub extern "C" fn probatum_prove(ptr: *const u8, len: usize) -> usize {
    let src = if len == 0 {
        String::new()
    } else {
        String::from_utf8_lossy(unsafe { std::slice::from_raw_parts(ptr, len) }).into_owned()
    };
    let out = check_source(&src);
    // Leaked deliberately: the pointer must outlive this call so JavaScript can
    // read it. A playground session is short and results are small.
    let boxed: &'static mut [u8] = Box::leak(out.into_bytes().into_boxed_slice());
    RESULT_PTR.store(boxed.as_mut_ptr() as usize, Ordering::Relaxed);
    boxed.len()
}

/// Address of the most recent JSON result.
#[no_mangle]
pub extern "C" fn probatum_result_ptr() -> *const u8 {
    RESULT_PTR.load(Ordering::Relaxed) as *const u8
}
