//! End-to-end integration tests: the whole pipeline, spec file → proof →
//! certificate → independent re-derivation → codegen, over the real
//! bundled examples.
//!
//! These tests are the acceptance criteria of the project itself:
//! if they pass, the tool does what its README claims.

use std::process::Command;

fn probatum_bin() -> Command {
    // `cargo test` sets CARGO_BIN_EXE_probatum for integration tests.
    Command::new(env!("CARGO_BIN_EXE_probatum"))
}

/// A per-test scratch directory. Keyed on process id AND a caller-provided
/// label: tests run concurrently in one process, and a shared directory let
/// one test's `.ic` files leak into another test's glob (caught in CI when
/// a deliberately-broken spec appeared in the "all examples prove" test).
fn workspace(label: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("ic-it-{}-{}", std::process::id(), label));
    // Start clean so leftovers from a previous run can't leak in.
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn examples_write_and_all_compile_proved() {
    let dir = workspace("examples");
    let out = probatum_bin()
        .args(["examples", dir.to_str().unwrap()])
        .output()
        .expect("run probatum examples");
    assert!(out.status.success(), "examples failed: {:?}", out);

    let entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().map(|x| x == "ic").unwrap_or(false))
        .collect();
    assert!(entries.len() >= 7, "expected ≥7 examples, got {:?}", entries);

    for spec in entries {
        let out_dir = dir.join(format!("build-{}", spec.file_stem().unwrap().to_string_lossy()));
        let out = probatum_bin()
            .args([
                "compile",
                spec.to_str().unwrap(),
                "--emit",
                "rust,go,dsl",
                "--out",
                out_dir.to_str().unwrap(),
            ])
            .output()
            .expect("run probatum compile");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "compile {:?} failed:\n{}",
            spec,
            stderr
        );
        assert!(
            stderr.contains("verdict: PROVED"),
            "{:?} was not proved:\n{}",
            spec,
            stderr
        );
        // Every artifact must exist.
        let stem = spec.file_stem().unwrap().to_string_lossy().to_string();
        for ext in ["cert", "rs", "go", "ic"] {
            let p = out_dir.join(format!("{}.{}", stem, ext));
            assert!(p.exists(), "missing artifact {:?}", p);
        }
    }
}

#[test]
fn certificate_roundtrip_through_independent_verify() {
    let dir = workspace("roundtrip");
    // Write the transfer example.
    let spec_path = dir.join("transfer.ic");
    std::fs::write(
        &spec_path,
        r#"
        spec transfer(a: int[0..15], b: int[0..15], amount: int[0..15])
          returns (x: int[0..15], y: int[0..15])
          requires amount <= a
          requires b + amount <= 15
          ensures x == a - amount
          ensures y == b + amount
          ensures x + y == a + b
          example (10, 5, 3) => (7, 8)
        {
          x := a - amount;
          y := b + amount;
        }
        "#,
    )
    .unwrap();

    let out_dir = dir.join("build");
    let compile = probatum_bin()
        .args([
            "compile",
            spec_path.to_str().unwrap(),
            "--out",
            out_dir.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(compile.status.success(), "{:?}", compile);

    // Independent verify against the GENERATED dsl (embeds the program).
    let verify = probatum_bin()
        .args([
            "verify",
            out_dir.join("transfer.cert").to_str().unwrap(),
            out_dir.join("transfer.ic").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&verify.stderr);
    assert!(
        verify.status.success(),
        "independent verify failed:\n{}",
        stderr
    );
    assert!(stderr.contains("VERIFIED"));
}

#[test]
fn tampered_certificate_is_rejected() {
    let dir = workspace("tamper");
    let spec_path = dir.join("inc.ic");
    std::fs::write(
        &spec_path,
        r#"
        spec inc(a: int[0..15]) returns (r: int[0..16])
          requires a < 15
          ensures r == a + 1
        { r := a + 1; }
        "#,
    )
    .unwrap();
    let out_dir = dir.join("build");
    let compile = probatum_bin()
        .args([
            "compile",
            spec_path.to_str().unwrap(),
            "--out",
            out_dir.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(compile.status.success());

    let cert_path = out_dir.join("inc.cert");
    let original = std::fs::read_to_string(&cert_path).unwrap();
    // Flip the verdict word.
    let tampered = original.replace("verdict: Proved", "verdict: Violated");
    assert_ne!(original, tampered, "test bug: nothing to tamper");
    std::fs::write(&cert_path, &tampered).unwrap();

    let replay = probatum_bin().args(["replay", cert_path.to_str().unwrap()]).output().unwrap();
    assert!(
        !replay.status.success(),
        "tampered certificate must not verify"
    );
}

#[test]
fn broken_body_is_refuted_with_counterexample() {
    let dir = workspace("refute");
    let spec_path = dir.join("off_by_one.ic");
    // Classic off-by-one: forgets the +1.
    std::fs::write(
        &spec_path,
        r#"
        spec off_by_one(a: int[0..15]) returns (r: int[0..16])
          requires a < 15
          ensures r == a + 1
        { r := a + 1 + 0 - 1; }
        "#,
    )
    .unwrap();
    let check = probatum_bin().args(["check", spec_path.to_str().unwrap()]).output().unwrap();
    let stdout = String::from_utf8_lossy(&check.stdout);
    assert!(
        !check.status.success(),
        "a refuted spec must exit non-zero"
    );
    assert!(stdout.contains("VIOLATED"), "stdout: {}", stdout);
    assert!(stdout.contains("counterexample") || stdout.contains("input:"));
}

#[test]
fn generated_rust_code_compiles_in_isolation() {
    // The emitted Rust must be valid, standalone Rust. Compile it in a
    // scratch crate with rustc.
    let dir = workspace("rustc");
    let spec_path = dir.join("half.ic");
    std::fs::write(
        &spec_path,
        r#"
        spec half(a: int[0..63]) returns (r: int[0..31])
          requires a % 2 == 0
          ensures r == a / 2
          example (4) => (2)
        {
          r := a / 2;
        }
        "#,
    )
    .unwrap();
    let out_dir = dir.join("build");
    let compile = probatum_bin()
        .args([
            "compile",
            spec_path.to_str().unwrap(),
            "--emit",
            "rust",
            "--out",
            out_dir.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(compile.status.success());

    let rs = out_dir.join("half.rs");
    let tmp = dir.join("half_lib.rs");
    std::fs::copy(&rs, &tmp).unwrap();
    let rustc = Command::new("rustc")
        .args(["--crate-type", "lib", "--edition", "2021", tmp.to_str().unwrap()])
        .output()
        .expect("rustc must be available");
    assert!(
        rustc.status.success(),
        "generated Rust failed to compile:\n{}",
        String::from_utf8_lossy(&rustc.stderr)
    );
}

#[test]
fn statistical_engine_never_claims_proof() {
    // A large domain with sampling only: verdict must NOT be "Proved".
    let dir = workspace("statistical");
    let spec_path = dir.join("big.ic");
    std::fs::write(
        &spec_path,
        r#"
        spec big(a: int[0..2000000]) returns (r: int[0..2000001])
          requires a < 2000000
          ensures r == a + 1
        { r := a + 1; }
        "#,
    )
    .unwrap();
    let check = probatum_bin()
        .args([
            "check",
            spec_path.to_str().unwrap(),
            "--engine",
            "statistical",
            "--samples",
            "5000",
        ])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&check.stdout);
    assert!(
        !check.status.success(),
        "sampling must never exit 0 (not a proof)"
    );
    assert!(
        stdout.contains("NOT A PROOF"),
        "must label itself honestly: {}",
        stdout
    );
}

#[test]
fn vacuous_spec_is_refused() {
    let dir = workspace("vacuous");
    let spec_path = dir.join("vacuous.ic");
    std::fs::write(
        &spec_path,
        r#"
        spec vacuous(a: int[0..15]) returns (r: int[0..16])
          requires a > 999
          ensures r == a + 1
        { r := a + 1; }
        "#,
    )
    .unwrap();
    let check = probatum_bin().args(["check", spec_path.to_str().unwrap()]).output().unwrap();
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&check.stdout),
        String::from_utf8_lossy(&check.stderr)
    );
    assert!(
        !check.status.success(),
        "vacuous spec must not be 'proved'"
    );
    assert!(
        combined.to_lowercase().contains("vacuous") || combined.to_lowercase().contains("unsatisfiable"),
        "must diagnose vacuity: {}",
        combined
    );
}

#[test]
fn negative_domains_cross_validate() {
    // Regression: negative ranges exercise sign-extension and the
    // MSB-flip signed comparator in the bitblaster. Added after a manual
    // probe found this path untested.
    let dir = workspace("negative");
    let spec_path = dir.join("negative_math.ic");
    std::fs::write(
        &spec_path,
        r#"
        spec negative_math(a: int[-8..7], b: int[-8..7]) returns (r: int[-32..31])
          ensures r == a - b + a
          ensures r == 2 * a - b
          example (-8, 7) => (-23)
          example (7, -8) => (22)
        {
          r := a - b + a;
        }
        "#,
    )
    .unwrap();
    let out_dir = dir.join("build");
    let compile = probatum_bin()
        .args([
            "compile",
            spec_path.to_str().unwrap(),
            "--out",
            out_dir.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&compile.stderr);
    assert!(compile.status.success(), "{}", stderr);
    assert!(stderr.contains("verdict: PROVED"), "{}", stderr);
    assert!(
        stderr.contains("cross-validated"),
        "negative domains must be proved by BOTH engines: {}",
        stderr
    );
}

#[test]
fn cegis_refinement_loop_recovers_from_prover_refutation() {
    // The genuine CEGIS loop: written as TWO INEQUALITIES so definitional
    // and piecewise extraction both fail and enumeration must run. The first
    // candidate (r == a) passes the given examples but the PROVER refutes it
    // at a=5; the loop must solve for the witness there and resume until the
    // synthesized program is certified.
    let dir = workspace("cegis");
    let spec_path = dir.join("cegis_step.ic");
    std::fs::write(
        &spec_path,
        r#"
        spec cegis_step(a: int[0..7]) returns (r: int[0..10])
          ensures r >= if a < 4 then a else 10
          ensures r <= if a < 4 then a else 10
          example (1) => (1)
          example (2) => (2)
        "#,
    )
    .unwrap();
    let out_dir = dir.join("build");
    let compile = probatum_bin()
        .args([
            "compile",
            spec_path.to_str().unwrap(),
            "--out",
            out_dir.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&compile.stderr);
    assert!(compile.status.success(), "{}", stderr);
    assert!(stderr.contains("verdict: PROVED"), "{}", stderr);
    // Must have needed more than one round: the first candidate is refuted.
    assert!(
        stderr.contains("CEGIS round(s)") && !stderr.contains("in 1 CEGIS round(s), 0 candidate"),
        "expected a real refinement loop, not a straight extraction: {}",
        stderr
    );
    // The synthesized program must be the conditional, not r == a.
    let dsl = std::fs::read_to_string(out_dir.join("cegis_step.ic")).unwrap();
    assert!(
        dsl.contains("if") && dsl.contains("then"),
        "synthesized program should be the conditional: {}",
        dsl
    );
}
