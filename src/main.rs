//! `ic` — The Intent Compiler.
//!
//! You write *behavioral intent* (preconditions, postconditions, invariants,
//! witnesses). `ic` verifies a program against that intent — or synthesizes
//! one — and emits a machine-checkable proof certificate that a separate,
//! independent verification path can re-derive from scratch.
//!
//! Commands:
//!   ic compile <spec.ic> [--emit rust,go,dsl] [--out DIR] [engine opts]
//!       Verify (or synthesize if the spec has no body) and emit artifacts:
//!       the program, a proof certificate, and target-language code.
//!
//!   ic check <spec.ic> [engine opts]
//!       Prove or refute the spec's body without emitting anything.
//!       Exits 0 if proved, 1 if violated, 2 if inconclusive.
//!
//!   ic verify <cert-file> <spec.ic> [engine opts]
//!       Independent verification: re-derive the proof from the spec alone
//!       and check it against the certificate. This is the path that does
//!       NOT trust the compiler.
//!
//!   ic replay <cert-file>
//!       Print a certificate's claims in human-readable form.
//!
//!   ic examples [DIR]
//!       Write the bundled example specs to DIR (default: ./examples).

mod ast;
mod bdd;
mod bitblast;
mod codegen;
mod eval;
mod lexer;
mod parser;
mod prove;
mod sema;
mod sha256;
mod synth;

use ast::Spec;
use prove::{Certificate, ProverOptions, Verdict};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(|s| s.as_str()) {
        Some("compile") => cmd_compile(&args[1..]),
        Some("check") => cmd_check(&args[1..]),
        Some("verify") => cmd_verify(&args[1..]),
        Some("replay") => cmd_replay(&args[1..]),
        Some("examples") => cmd_examples(&args[1..]),
        Some("--version") | Some("version") | Some("-V") => {
            println!("ic {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Some("--help") | Some("help") | Some("-h") | None => {
            print_help();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("ic: unknown command `{}`\n", other);
            print_help();
            ExitCode::from(2)
        }
    }
}

fn print_help() {
    println!(
        "ic — the intent compiler

Write behavioral intent. Get verified code.

USAGE:
    ic compile <spec.ic> [--emit rust,go,dsl] [--out DIR] [opts]
    ic check   <spec.ic> [opts]
    ic verify  <cert-file> <spec.ic> [opts]
    ic replay  <cert-file>
    ic examples [DIR]

OPTIONS (proof engines):
    --engine auto|exhaustive|bdd|statistical   choose engine (default: auto)
    --budget N          exhaustive input budget       (default: 100000000)
    --bdd-budget N      BDD node budget               (default: 5000000)
    --samples N         statistical samples           (default: 100000)
    --confidence C      statistical confidence 0..1   (default: 0.95)

EXIT CODES:
    0  proved / verified
    1  violated (counterexample exists)
    2  inconclusive, gave up, or usage error

The spec language:
    spec name(a: int[0..255], b: int[0..9])
      returns (x: int[0..255])
      requires a > b              // precondition (inputs outside: out of domain)
      ensures  x == a - b         // postcondition (must hold for ALL inputs)
      ensures  x + b == a         // invariants read the same way
      example (10, 3) => (7)      // concrete witness (checked first)
    {{ x := a - b; }}               // optional: omit and ic synthesizes it"
    );
}

// ---------------------------------------------------------------------------
// argument parsing
// ---------------------------------------------------------------------------

struct Opts {
    engine: String,
    exhaustive_budget: u128,
    bdd_budget: usize,
    samples: u64,
    confidence: f64,
    emit: Vec<String>,
    out: Option<PathBuf>,
    positional: Vec<String>,
}

fn parse_opts(args: &[String]) -> Result<Opts, String> {
    let mut o = Opts {
        engine: "auto".into(),
        exhaustive_budget: 100_000_000,
        bdd_budget: 5_000_000,
        samples: 100_000,
        confidence: 0.95,
        emit: vec!["rust".into(), "go".into(), "dsl".into()],
        out: None,
        positional: Vec::new(),
    };
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        match a.as_str() {
            "--engine" => {
                i += 1;
                o.engine = args.get(i).cloned().ok_or("--engine needs a value")?;
            }
            "--budget" => {
                i += 1;
                o.exhaustive_budget = args
                    .get(i)
                    .and_then(|v| v.parse().ok())
                    .ok_or("--budget needs a number")?;
            }
            "--bdd-budget" => {
                i += 1;
                o.bdd_budget = args
                    .get(i)
                    .and_then(|v| v.parse().ok())
                    .ok_or("--bdd-budget needs a number")?;
            }
            "--samples" => {
                i += 1;
                o.samples = args
                    .get(i)
                    .and_then(|v| v.parse().ok())
                    .ok_or("--samples needs a number")?;
            }
            "--confidence" => {
                i += 1;
                o.confidence = args
                    .get(i)
                    .and_then(|v| v.parse().ok())
                    .ok_or("--confidence needs a number")?;
            }
            "--emit" => {
                i += 1;
                let v = args.get(i).ok_or("--emit needs a value")?;
                o.emit = v.split(',').map(|s| s.trim().to_string()).collect();
            }
            "--out" | "-o" => {
                i += 1;
                o.out = Some(PathBuf::from(args.get(i).ok_or("--out needs a path")?));
            }
            other if other.starts_with('-') => {
                return Err(format!("unknown flag `{}`", other));
            }
            _ => o.positional.push(a.clone()),
        }
        i += 1;
    }
    Ok(o)
}

fn to_prover_opts(o: &Opts) -> ProverOptions {
    ProverOptions {
        exhaustive_budget: o.exhaustive_budget,
        bdd_budget: o.bdd_budget,
        samples: o.samples,
        confidence: o.confidence,
        engine: o.engine.clone(),
    }
}

fn read_spec(path: &Path) -> Result<Spec, String> {
    let src = std::fs::read_to_string(path).map_err(|e| format!("cannot read {:?}: {}", path, e))?;
    let spec = parser::parse(&src).map_err(|e| format!("{}:{}: {}", path.display(), 1, e))?;
    sema::analyze(&spec).map_err(|e| format!("{}: {}", path.display(), e))?;
    Ok(spec)
}

// ---------------------------------------------------------------------------
// ic check
// ---------------------------------------------------------------------------

fn cmd_check(args: &[String]) -> ExitCode {
    let o = match parse_opts(args) {
        Ok(o) => o,
        Err(e) => return usage_err(&e),
    };
    let Some(spec_path) = o.positional.first() else {
        return usage_err("check needs a spec file");
    };
    let spec = match read_spec(Path::new(spec_path)) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::from(2);
        }
    };
    let Some(body) = spec.body.clone() else {
        eprintln!(
            "error: {} has no body — run `ic compile {}` to synthesize one",
            spec_path, spec_path
        );
        return ExitCode::from(2);
    };
    report_verdict(&spec, &prove::prove(&spec, &body, &to_prover_opts(&o)))
}

// ---------------------------------------------------------------------------
// ic compile
// ---------------------------------------------------------------------------

fn cmd_compile(args: &[String]) -> ExitCode {
    let o = match parse_opts(args) {
        Ok(o) => o,
        Err(e) => return usage_err(&e),
    };
    let Some(spec_path) = o.positional.first() else {
        return usage_err("compile needs a spec file");
    };
    let spec = match read_spec(Path::new(spec_path)) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::from(2);
        }
    };

    let popts = to_prover_opts(&o);

    // Obtain a body: from the spec, or by synthesis.
    let (body, synth_stats) = match spec.body.clone() {
        Some(b) => (b, None),
        None => {
            eprintln!(
                "ic: no body in spec — synthesizing one from intent (this is the fun part)..."
            );
            match synth::synthesize(&spec, &popts) {
                Ok(s) => {
                    eprintln!(
                        "ic: synthesized via {} in {} CEGIS round(s), {} candidate(s) generated, {} pruned as equivalent",
                        s.stats.strategy,
                        s.stats.cegis_rounds,
                        s.stats.candidates_generated,
                        s.stats.candidates_pruned
                    );
                    (s.body, Some(s.stats))
                }
                Err(e) => {
                    eprintln!("synthesis failed: {}", e);
                    if let Some(inputs) = e.unrealizable_input() {
                        let pairs: Vec<String> =
                            inputs.iter().map(|(k, v)| format!("{}={}", k, v)).collect();
                        eprintln!(
                            "ic: the contract is IMPOSSIBLE at input ({}) — no output within \
                             the declared result domains can satisfy every `ensures` clause. \
                             Fix the spec, not the program.",
                            pairs.join(", ")
                        );
                    }
                    return ExitCode::from(2);
                }
            }
        }
    };

    // Prove (synthesis already proved, but we re-prove from the same body
    // so the certificate always describes a fresh, explicit proof run).
    eprintln!("ic: proving...");
    let proof = prove::prove(&spec, &body, &popts);

    let verdict_line = match &proof.verdict {
        Verdict::Proved => "PROVED".to_string(),
        Verdict::Violated => "VIOLATED".to_string(),
        Verdict::NoViolationFound => "NO VIOLATION FOUND (not a proof)".to_string(),
        Verdict::GaveUp { reason } => format!("GAVE UP: {}", reason),
    };
    eprintln!("ic: verdict: {}", verdict_line);
    for e in &proof.engines {
        let nodes = e.nodes.map(|n| format!(" nodes={}", n)).unwrap_or_default();
        eprintln!(
            "ic:   engine {:<20} {:<28} checked={}{}",
            e.engine,
            format!("{:?}", e.verdict),
            e.checked,
            nodes
        );
        for n in &e.notes {
            eprintln!("ic:     {}", n);
        }
    }
    if proof.cross_validated {
        eprintln!("ic: ✓ cross-validated: two independent complete engines agree");
    }

    if !matches!(proof.verdict, Verdict::Proved | Verdict::Violated) {
        eprintln!("ic: refusing to emit artifacts for an inconclusive verdict");
        return ExitCode::from(2);
    }

    // Certificate.
    let program_src = render_program(&spec, &body);
    let program_digest = sha256::sha256_hex(program_src.as_bytes());
    let spec_digest = {
        // Hash the canonical spec text, not the file bytes (comments shouldn't
        // invalidate a certificate).
        let canonical = canonical_spec_text(&spec);
        sha256::sha256_hex(canonical.as_bytes())
    };
    let cert = Certificate {
        spec_sha256: spec_digest.clone(),
        program_sha256: program_digest.clone(),
        spec_name: spec.name.clone(),
        verdict: format!("{:?}", proof.verdict),
        engines: proof
            .engines
            .iter()
            .map(|e| {
                (
                    e.engine.clone(),
                    format!("{:?}", e.verdict),
                    e.checked,
                    e.nodes,
                )
            })
            .collect(),
        cross_validated: proof.cross_validated,
        pre_witness: proof.pre_witness.clone(),
        counterexample: proof.counterexample.clone(),
        stat_bound: proof.stat_bound,
        cert_sha256: String::new(),
    }
    .seal();

    // Output directory.
    let out_dir = o
        .out
        .clone()
        .unwrap_or_else(|| PathBuf::from(format!("{}-verified", spec.name)));
    if let Err(e) = std::fs::create_dir_all(&out_dir) {
        eprintln!("ic: cannot create {:?}: {}", out_dir, e);
        return ExitCode::from(2);
    }

    // Write artifacts.
    let base = out_dir.join(&spec.name);
    let write = |path: PathBuf, contents: &str| -> Result<(), String> {
        std::fs::write(&path, contents).map_err(|e| format!("cannot write {:?}: {}", path, e))
    };

    let mut written = Vec::new();
    let cert_path = base.with_extension("cert");
    let proof_status = if proof.verdict == Verdict::Proved {
        "proved"
    } else {
        "refuted"
    };
    if write(cert_path.clone(), &cert.render()).is_err() {
        eprintln!("ic: failed to write certificate");
        return ExitCode::from(2);
    }
    written.push(cert_path);

    // The DSL artifact is ALWAYS written, even if not requested: it embeds
    // the program, and `ic verify` needs it to re-derive the proof against
    // the certificate. Requesting `--emit rust,go` must not break verify.
    let mut targets: Vec<String> = o.emit.clone();
    if !targets.iter().any(|t| matches!(t.as_str(), "dsl" | "ic")) {
        targets.push("dsl".into());
    }

    for lang_name in &targets {
        let Some(lang) = codegen::TargetLang::from_name(lang_name) else {
            eprintln!("ic: unknown target `{}` (want rust, go, or dsl)", lang_name);
            return ExitCode::from(2);
        };
        match codegen::emit(&spec, &body, lang, &cert.cert_sha256) {
            Ok(code) => {
                let path = base.with_extension(lang.file_extension());
                if write(path.clone(), &code).is_err() {
                    eprintln!("ic: failed to write {:?}", path);
                    return ExitCode::from(2);
                }
                written.push(path);
            }
            Err(e) => {
                eprintln!("ic: codegen for {} failed: {}", lang_name, e);
                return ExitCode::from(2);
            }
        }
    }

    eprintln!("ic: {} — {} in {:?}", proof_status, spec.name, out_dir);
    for p in &written {
        eprintln!("ic:   {}", p.display());
    }
    if let Some(st) = &synth_stats {
        eprintln!(
            "ic:   (synthesized: {} strategy, {} examples used)",
            st.strategy, st.examples_used
        );
    }
    eprintln!(
        "ic:   cert-sha256: {}",
        &cert.cert_sha256[..cert.cert_sha256.len().min(32)]
    );

    if proof.verdict == Verdict::Proved {
        ExitCode::SUCCESS
    } else {
        eprintln!("ic: WARNING: emitted artifacts describe a REFUTED program (educational; do not ship)");
        ExitCode::from(1)
    }
}

// ---------------------------------------------------------------------------
// ic verify — the path that does not trust the compiler
// ---------------------------------------------------------------------------

fn cmd_verify(args: &[String]) -> ExitCode {
    let o = match parse_opts(args) {
        Ok(o) => o,
        Err(e) => return usage_err(&e),
    };
    let (Some(cert_path), Some(spec_path)) = (o.positional.first(), o.positional.get(1)) else {
        return usage_err("verify needs <cert-file> <spec.ic>");
    };

    let cert_text = match std::fs::read_to_string(cert_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("ic: cannot read certificate: {}", e);
            return ExitCode::from(2);
        }
    };
    let cert = match Certificate::parse(&cert_text) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("ic: certificate INVALID: {}", e);
            return ExitCode::from(2);
        }
    };
    eprintln!("ic: certificate digest: OK");

    let spec = match read_spec(Path::new(spec_path)) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::from(2);
        }
    };

    // Spec digest check.
    let canonical = canonical_spec_text(&spec);
    let digest = sha256::sha256_hex(canonical.as_bytes());
    if digest != cert.spec_sha256 {
        eprintln!(
            "ic: SPEC MISMATCH: certificate was issued for a different spec\n\
             \tic:   cert says:    {}\n\
             \tic:   this spec is: {}",
            cert.spec_sha256, digest
        );
        return ExitCode::from(2);
    }
    eprintln!("ic: spec digest: OK");

    // Re-derive the proof from the spec alone.
    let Some(body) = spec.body.clone() else {
        eprintln!(
            "ic: this spec file has no body.\n\
             \tIf the program was synthesized, verify against the generated DSL file\n\
             \t(e.g. <out>/<name>.ic) — it embeds the program, and its contract\n\
             \tdigest will still match the original spec's certificate."
        );
        return ExitCode::from(2);
    };
    let proof = prove::prove(&spec, &body, &to_prover_opts(&o));

    // Compare.
    let derived_verdict = format!("{:?}", proof.verdict);
    if derived_verdict != cert.verdict {
        eprintln!(
            "ic: VERDICT MISMATCH: certificate says {}, re-derivation says {}",
            cert.verdict, derived_verdict
        );
        return ExitCode::from(2);
    }
    eprintln!("ic: verdict re-derived: {} — matches certificate", derived_verdict);

    // Program digest check (binds the certificate to the exact program).
    let program_src = render_program(&spec, &body);
    let pd = sha256::sha256_hex(program_src.as_bytes());
    if pd != cert.program_sha256 {
        eprintln!(
            "ic: PROGRAM MISMATCH: certificate binds to a different program\n\
             \tic:   cert says:     {}\n\
             \tic: this program is: {}",
            cert.program_sha256, pd
        );
        return ExitCode::from(2);
    }
    eprintln!("ic: program digest: OK");

    if proof.verdict == Verdict::Proved {
        eprintln!("ic: ✓ VERIFIED — certificate is authentic and the proof re-derives");
        ExitCode::SUCCESS
    } else {
        eprintln!("ic: certificate authentic, but verdict is {}", cert.verdict);
        if let Some(cx) = &cert.counterexample {
            eprintln!("ic: counterexample: {:?}", cx.inputs);
        }
        ExitCode::from(1)
    }
}

// ---------------------------------------------------------------------------
// ic replay
// ---------------------------------------------------------------------------

fn cmd_replay(args: &[String]) -> ExitCode {
    let Some(cert_path) = args.first() else {
        return usage_err("replay needs a certificate file");
    };
    let text = match std::fs::read_to_string(cert_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("ic: cannot read certificate: {}", e);
            return ExitCode::from(2);
        }
    };
    match Certificate::parse(&text) {
        Ok(c) => {
            println!("{}", c.render());
            println!("(digest verified — this certificate is authentic)");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("ic: certificate INVALID: {}", e);
            ExitCode::from(2)
        }
    }
}

// ---------------------------------------------------------------------------
// ic examples
// ---------------------------------------------------------------------------

const EXAMPLES: &[(&str, &str)] = &[
    (
        "transfer_funds.ic",
        r#"// Money in, money out. Nothing created, nothing destroyed.
//
// The invariant `x + y == a + b` is NOT something the body states — it is
// something the PROVER derives from the two definitional clauses plus the
// precondition. This is what "proof-carrying intent" looks like.
spec transfer_funds(a: int[0..255], b: int[0..255], amount: int[0..255])
  returns (x: int[0..255], y: int[0..255])
  requires amount <= a
  requires b + amount <= 255
  ensures  x == a - amount
  ensures  y == b + amount
  ensures  x + y == a + b
  example (100, 50, 25) => (75, 75)
  example (0, 0, 0) => (0, 0)
{
  x := a - amount;
  y := b + amount;
}
"#,
    ),
    (
        "saturating_sub.ic",
        r#"// Subtraction that clamps at zero — never goes negative.
// No body: ic synthesizes one that satisfies the contract for ALL inputs.
spec saturating_sub(a: int[0..255], b: int[0..255])
  returns (r: int[0..255])
  ensures  r == if a >= b then a - b else 0
  ensures  r <= a
  example (10, 3) => (7)
  example (3, 10) => (0)
"#,
    ),
    (
        "max_value.ic",
        r#"// The classic, specified as three honest properties instead of an formula.
// ic finds `max(a, b)` (or an equivalent) and the PROVER certifies it.
spec max_value(a: int[0..127], b: int[0..127])
  returns (r: int[0..127])
  ensures  r >= a
  ensures  r >= b
  ensures  r == a || r == b
  example (3, 9) => (9)
  example (9, 3) => (9)
  example (5, 5) => (5)
"#,
    ),
    (
        "clamp.ic",
        r#"// Clamp into a range — the shape of every validated input ever written.
spec clamp(v: int[0..255], lo: int[0..255], hi: int[0..255])
  returns (r: int[0..255])
  requires lo <= hi
  ensures  r >= lo
  ensures  r <= hi
  ensures  if v >= lo && v <= hi then r == v else r == if v < lo then lo else hi
  example (50, 10, 20) => (20)
  example (15, 10, 20) => (15)
  example (5, 10, 20) => (10)
"#,
    ),
    (
        "safe_reciprocal.ic",
        r#"// Division that can NEVER fault: the precondition excludes the divisor
// being zero, and the prover checks that exclusion actually holds for
// every input it claims to protect. (Division uses the exhaustive engine;
// the BDD engine honestly declines rather than guessing.)
spec safe_reciprocal(a: int[0..255], b: int[0..255])
  returns (r: int[0..255])
  requires b != 0
  requires a / b <= 255
  ensures  r == a / b
  example (10, 2) => (5)
  example (9, 3) => (3)
{
  r := a / b;
}
"#,
    ),
    (
        "weighted_sum.ic",
        r#"// A tiny perceptron cell — the shape of every ML kernel, but verified.
// 2*a + b, for all a, b in the domain, proven not merely tested.
spec weighted_sum(a: int[0..63], b: int[0..63])
  returns (r: int[0..191])
  ensures  r == 2 * a + b
  example (1, 1) => (3)
  example (10, 5) => (25)
"#,
    ),
    (
        "consensus.ic",
        r#"// Two-of-three majority — the workhorse of fault-tolerant systems,
// expressed as properties and synthesized into code.
spec consensus(v1: int[0..1], v2: int[0..1], v3: int[0..1])
  returns (r: int[0..1])
  ensures  r == if v1 + v2 + v3 >= 2 then 1 else 0
  example (1, 1, 0) => (1)
  example (1, 0, 0) => (0)
  example (1, 1, 1) => (1)
"#,
    ),
];

fn cmd_examples(args: &[String]) -> ExitCode {
    let dir = PathBuf::from(args.first().cloned().unwrap_or_else(|| "examples".into()));
    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("ic: cannot create {:?}: {}", dir, e);
        return ExitCode::from(2);
    }
    for (name, src) in EXAMPLES {
        let path = dir.join(name);
        if let Err(e) = std::fs::write(&path, src) {
            eprintln!("ic: cannot write {:?}: {}", path, e);
            return ExitCode::from(2);
        }
        println!("wrote {}", path.display());
    }
    println!("\nTry:  ic compile {} --emit rust,go", dir.join("transfer_funds.ic").display());
    ExitCode::SUCCESS
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn usage_err(msg: &str) -> ExitCode {
    eprintln!("ic: {}\n", msg);
    print_help();
    ExitCode::from(2)
}

fn report_verdict(spec: &Spec, proof: &prove::ProofResult) -> ExitCode {
    println!("spec: {}", spec.name);
    for e in &proof.engines {
        let nodes = e.nodes.map(|n| format!(" nodes={}", n)).unwrap_or_default();
        println!(
            "  engine {:<20} {:<28} checked={}{}",
            e.engine,
            format!("{:?}", e.verdict),
            e.checked,
            nodes
        );
        for n in &e.notes {
            println!("    {}", n);
        }
    }
    if proof.cross_validated {
        println!("  cross-validated: two independent complete engines agree");
    }
    match &proof.verdict {
        Verdict::Proved => {
            println!("VERDICT: PROVED — every input satisfying `requires` meets every `ensures`");
            if let Some(w) = &proof.pre_witness {
                if !w.is_empty() {
                    let pairs: Vec<String> =
                        w.iter().map(|(k, v)| format!("{}={}", k, v)).collect();
                    println!("  (precondition satisfiable; witness: {})", pairs.join(", "));
                }
            }
            ExitCode::SUCCESS
        }
        Verdict::Violated => {
            println!("VERDICT: VIOLATED — a concrete counterexample exists:");
            if let Some(cx) = &proof.counterexample {
                let pairs: Vec<String> = cx
                    .inputs
                    .iter()
                    .map(|(k, v)| format!("{}={}", k, v))
                    .collect();
                println!("  input:  {}", pairs.join(", "));
                println!("  cause:  {}", cx.violation);
            }
            ExitCode::from(1)
        }
        Verdict::NoViolationFound => {
            println!(
                "VERDICT: NO VIOLATION FOUND in samples — NOT A PROOF"
            );
            if let Some((bound, conf)) = proof.stat_bound {
                println!(
                    "  violation rate < {:.3e} with {:.0}% confidence",
                    bound,
                    conf * 100.0
                );
            }
            ExitCode::from(2)
        }
        Verdict::GaveUp { reason } => {
            println!("VERDICT: GAVE UP — {}", reason);
            ExitCode::from(2)
        }
    }
}

fn render_program(spec: &Spec, body: &[ast::Assign]) -> String {
    let mut s = format!("program {}(", spec.name);
    s.push_str(
        &spec
            .params
            .iter()
            .map(|b| format!("{}: {}", b.name, b.ty))
            .collect::<Vec<_>>()
            .join(", "),
    );
    s.push_str(") -> (");
    s.push_str(
        &spec
            .results
            .iter()
            .map(|b| format!("{}: {}", b.name, b.ty))
            .collect::<Vec<_>>()
            .join(", "),
    );
    s.push_str(")\n");
    for a in body {
        s.push_str(&format!("  {} := {};\n", a.name, a.value));
    }
    s
}

/// Canonical text of a spec's CONTRACT (never the body).
///
/// Comments and formatting don't change meaning, and the body is bound
/// separately by `program-sha256` — so this function deliberately excludes
/// the body. That split is what lets `ic verify` check a synthesized spec
/// against the *original* body-less file: contract digest matches the
/// intent, program digest binds the synthesized code.
fn canonical_spec_text(spec: &Spec) -> String {
    let mut s = format!("spec {}(", spec.name);
    s.push_str(
        &spec
            .params
            .iter()
            .map(|b| format!("{}: {}", b.name, b.ty))
            .collect::<Vec<_>>()
            .join(", "),
    );
    s.push_str(") returns (");
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
        s.push_str(&format!("requires {}\n", c));
    }
    for c in &spec.ensures {
        s.push_str(&format!("ensures {}\n", c));
    }
    for e in &spec.examples {
        let ins: Vec<String> = e.inputs.iter().map(|v| v.to_string()).collect();
        let outs: Vec<String> = e.outputs.iter().map(|v| v.to_string()).collect();
        s.push_str(&format!("example ({}) => ({})\n", ins.join(", "), outs.join(", ")));
    }
    s
}
