# Architecture

How `ic` is put together, and why each piece is shaped the way it is.

```
            spec.ic                          (the source of truth)
               │
     ┌─────────▼─────────┐
     │  lexer → parser   │  src/lexer.rs, src/parser.rs
     └─────────┬─────────┘
               │  AST
     ┌─────────▼─────────┐
     │  semantic analysis│  src/sema.rs   name resolution, typing,
     └─────────┬─────────┘  static range checks (reject only what is
               │             DEFINITELY broken; defer the rest to proof)
               │
     ┌─────────▼─────────┐
     │    evaluator      │  src/eval.rs   ← THE SPECIFICATION. One place
     └─────────┬─────────┘    defines what "correct" means. Every engine
               │              and every generated artifact agrees with it
               │              or is wrong by definition.
      ┌────────┴────────┐
      │                 │
┌─────▼──────┐   ┌──────▼───────┐   body present?
│  prover    │   │ synthesizer  │───────────────┐
│ src/prove  │   │  src/synth   │               │
└─────┬──────┘   └──────┬───────┘               │
      │                 │  CEGIS loop:          │
      │                 │  extract → enumerate  │
      │                 │  → prove → refine ◄───┘
      │                 │    with counterexample
┌─────▼─────────────────▼─────┐
│      engine ladder          │
│  1. exhaustive  (complete)  │   src/prove.rs::run_exhaustive
│  2. bdd-symbolic(complete)  │   src/bdd.rs + src/bitblast.rs
│  3. statistical (NOT proof) │   src/prove.rs::run_statistical
│                             │
│  ── cross-validation ──     │   engines must AGREE or we refuse
└─────────────┬───────────────┘
              │
      ┌───────▼────────┐      ┌──────────────────┐
      │  certificate   │──────│  ic verify       │  re-derives the proof
      │  SHA-256 sealed│      │  (does NOT trust │  from the spec alone and
      └───────┬────────┘      │   the compiler)  │  checks the certificate
              │               └──────────────────┘
      ┌───────▼────────┐
      │    codegen     │  src/codegen.rs → Rust / Go / DSL
      └────────────────┘
```

---

## The evaluator is the specification

There is exactly **one** definition of what a spec means:
[`src/eval.rs`](src/eval.rs). Not the parser's, not the BDD engine's, not the
synthesizer's — the evaluator's.

This is a deliberate, load-bearing choice. If each engine carried its own
notion of semantics, "cross-validation" would be comparing two guesses. Because
they all defer to `eval.rs`, agreement between the exhaustive engine (which
speaks i64 arithmetic) and the BDD engine (which speaks boolean circuits) is
genuine independent evidence, not a tautology.

The evaluator's semantics, stated plainly:

- **`requires` false ⇒ out of domain.** Not a violation. The contract says
  nothing about inputs it excludes. `ic` skips them — it does not "prove" them.
- **`ensures` false ⇒ violation.** A concrete counterexample exists.
- **Division by zero, overflow, out-of-range result ⇒ fault**, which counts as
  a violation. A program that crashes on a valid input has broken its contract.
- **`if` is lazy; `&&`/`||` short-circuit.** `if b == 0 then 0 else a / b` is
  safe by construction, and the evaluator — plus the bitblaster's fault signal —
  both model this exactly.

Every engine, and every generated artifact, agrees with this file or is wrong.

---

## Engine ladder and cross-validation

[`src/prove.rs`](src/prove.rs) runs engines in a ladder and combines their
verdicts:

1. **Exhaustive** — an odometer walks every input in the product domain,
   skips those failing `requires`, runs the evaluator on the rest. Complete
   whenever it terminates within `--budget`. This engine is, by construction,
   the definition of correctness.
2. **BDD-symbolic** — [`src/bitblast.rs`](src/bitblast.rs) compiles the whole
   contract into one boolean function over **interleaved-ordered** variables
   (Bryant ordering: bit 0 of every parameter adjacent, then bit 1, …), then
   [`src/bdd.rs`](src/bdd.rs) asks whether the "bad state" function is
   satisfiable. UNSAT ⇒ *no input in the entire domain* violates the contract.
   Counterexamples it finds are extracted and **confirmed with the evaluator**
   before being reported — a BDD bug cannot produce a bogus certificate.
3. **Statistical** — SplitMix64 (deterministic, so certificates are
   reproducible) sampling with a Clopper–Pearson upper bound. It never says
   "proved". It says "no violation found in N samples; violation rate < X at
   confidence Y" and exits 2.

**Cross-validation:** when two complete engines both ran, their verdicts must
match. A mismatch is an *internal error* — `ic` refuses to certify rather than
pick a winner. This is the single most important property of the design, and
it has caught two real bugs (below).

---

## What the net caught

The safety net is not theater. During development it caught **four** genuine
bugs in `ic`'s own proof machinery — none produced a false proof (the net
held), but each would have produced confusing or wrong behaviour:

1. **BDD `ite` cache-key truncation.** The memoization key for the ternary
   `ite` primitive packed its three operands into a two-slot tuple, silently
   dropping one. Distinct `ite` calls could collide and return the wrong
   subgraph. *Symptom:* exhaustive said `Proved`, BDD said `Violated`.
   *Fix:* a proper 4-tuple key.
2. **Bitblaster circuit width.** Arithmetic circuits were sized from the
   *result's* static range alone. In a chain like `a + 1 - 1`, the intermediate
   `a+1` is wider than the final range, and `sign_extend` tripped its own
   assertion. *Fix:* circuit width is now `max(result range, operand widths)`.
3. **`select()` was fault-unsound.** It OR-ed the fault signals of *both*
   branches, so an out-of-bounds read in a branch the guard excludes still
   leaked a fault. *Symptom:* the symbolic engine accused a **correct** program
   of a contract violation. *Found by:* the rule that every symbolic
   counterexample must be confirmed by the evaluator before it is reported.
   *Fix:* the fault is selected too — lazy, mirroring the evaluator.
4. **Array substitution skipped quantifier bodies.** `subst_array_write`
   returned `forall`/`exists`/`sum` bodies unchanged, on the mistaken reasoning
   that a bound variable might shadow the write's index (the type checker
   already rejects that). *Symptom:* `forall i: r[i] == s[3-i]` kept the **old**
   `r` after the writes to `r`, again accusing a correct program.
   *Fix:* recurse into binders.

All four are documented in the commit history and covered by regression tests.

---

## Synthesis: from intent to program

[`src/synth.rs`](src/synth.rs) never blesses its own output — every candidate
still has to survive the full prover. The strategy ladder, first success wins:

1. **Definitional extraction.** If `ensures` says `x == e` for parameter-only
   `e`, then `x := e` *is* the answer; the spec handed us the program. Chains
   (`y == f(x)` where `x` is itself defined) resolve by transitive
   substitution; cycles are reported, not guessed around.
2. **Piecewise extraction.** `if c then (r == a) else (r == b)` — with
   arbitrarily nested `if`s — is a definition: `r := if c then a else b`.
   Real intent is full of these ("clamp", "if valid then value else default").
3. **Enumerative search.** A typed grammar (int and bool sorts) grows
   candidates by increasing size. Candidates are filtered against accumulated
   examples and **deduplicated by their behavior on a sample** — structurally
   different but observationally identical candidates collapse, which is what
   keeps the space from exploding.
4. **CEGIS refinement.** A candidate that passes every example is handed to the
   prover. If the prover refutes it, `ic` takes the counterexample input and
   *solves for a valid output* there by bounded enumeration over the declared
   result domains (checking every `ensures`). The new witness joins the example
   set and the search resumes, strictly smarter.

**Failure is categorized honestly:**

- *Search exhaustion* ⇒ "no program of size ≤ N found" — **not** a proof that
  none exists. Reported as a bound, with the search statistics.
- *Unrealizable input* ⇒ a concrete input where **no** output tuple can satisfy
  the contract. This is a genuine impossibility proof about the *spec*, and `ic`
  prints that input and tells you to fix the spec, not the program.

---

## Certificates

A certificate is canonical, deterministic text — no timestamps, no paths, no
nondeterminism — bound by SHA-256 (hand-written, FIPS 180-4, test-vector
verified in [`src/sha256.rs`](src/sha256.rs)):

```
ic-cert-1
spec: transfer_funds
spec-sha256: <hash of the CONTRACT, comments and formatting excluded>
program-sha256: <hash of the PROGRAM>
verdict: Proved
cross-validated: true
precondition: SATISFIABLE
witness: a=0, b=0, amount=0
engine: exhaustive verdict=Proved checked=5625216
engine: bdd-symbolic verdict=Proved checked=134217728 nodes=17454
cert-sha256: <hash over everything above>
```

The contract digest deliberately **excludes the body**: that split is what lets
`ic verify` check a *synthesized* spec against the original body-less file — the
contract digest matches the intent, the program digest binds the synthesized
code.

`ic verify` re-derives the proof from the spec alone and compares: digest, then
verdict, then program hash. Any mismatch — one byte of the spec, one line of the
program — and it refuses. An integration test tampers with a certificate by a
single character and asserts rejection.

---

## Design rules

These are the invariants the code is organized around. Breaking one is a bug,
even if tests pass.

- **A declined engine is never a false proof.** Unsupported fragment or blown
  budget ⇒ `GaveUp`, never `Proved`.
- **A statistical result is never labeled a proof.** It exits 2 and says so.
- **A vacuous precondition is never "proved".** Refused explicitly.
- **On engine disagreement, refuse to certify.** Never pick a winner.
- **Every BDD counterexample is confirmed by the evaluator** before it is
  reported.
- **The evaluator is the only semantics.** No engine defines its own.
- **Exhaustive and BDD share no code path** — only `eval.rs` as their common
  specification. That's what makes their agreement meaningful.
- **Synthesis never trusts itself.** The prover decides.

---

## Trust boundary

What you must trust to believe a certificate:

1. **The Rust compiler and runtime** (for the `ic` binary you ran).
2. **The evaluator's semantics** — [`src/eval.rs`](src/eval.rs), a few hundred
   lines, deliberately boring, heavily unit-tested.
3. **The certificate digest** — hand-written SHA-256 with FIPS test vectors.

What you do **not** have to trust:

- The synthesizer (it can only propose; the prover disposes).
- The BDD engine alone (cross-validated against the exhaustive engine, or
  declining honestly).
- The compiler that issued the certificate (`ic verify` re-derives independently).
- Any external SMT solver or library — there are none. Zero dependencies.
