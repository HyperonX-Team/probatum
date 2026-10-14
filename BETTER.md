# Is it better than Dafny, Verus, Kani or Lean?

Not overall — that would be a lie, and a verifier that lies about itself is
worthless. It is better on **specific axes**, and this page names them, names
the axes it loses, and gives the command to check every claim yourself.

The rule this page follows: **no number appears here that you cannot reproduce
in one command.**

---

## The scorecard

| Axis | probatum | Dafny / Verus / Kani | Who wins |
|---|---|---|---|
| **Diagnosis when a proof fails** | minimal counterexample, both sides of the failing comparison reported numerically, the construct to edit named | the obligation that failed; a solver model that is an artifact of its search | **probatum** — see below |
| **Time to first proof** | `cargo install probatum` — one command, no setup, no external solver | .NET + Z3 (Dafny), a pinned Rust nightly + Z3 (Verus), CBMC (Kani) | **probatum** |
| **Try it without installing anything** | in progress: a browser playground | not offered by any of the four | **probatum** (once it ships) |
| **Can it say "unknown"?** | no — inside the fragment both engines decide, or the tool says it declined and why | yes: solver timeout, unwinding bound, "might not hold" | **probatum**, inside its fragment |
| **Trust surface** | ~8.9k code lines, zero dependencies, two independent engines, certificate re-derived from the spec alone | Z3 and CBMC are large trusted components; the proof is only as good as the solver's answer | **probatum**, inside its fragment |
| **Synthesizes the program from the contract** | yes (CEGIS) | no | **probatum** |
| **Unbounded integers, recursion, heap** | **no** | yes | **Dafny / Verus / Kani** |
| **Verifies code you already wrote, in Rust** | no — you write the intent, and it emits Rust | **Verus and Kani verify real Rust** | **Verus / Kani** |
| **Mathematics, dependent types, deep proofs** | not attempted | **Lean 4** | **Lean** |
| **Ecosystem, books, courses, jobs** | none | years of it | **Dafny / Lean** |

Read the last four rows before the first four. If you need any of them, use the
established tool — probatum will not help you, and pretending otherwise would
waste your afternoon.

---

## Axis 1: diagnosis

This is the axis probatum was built to win, because it is the one the
SMT-backed tools lose *by construction*: when Z3 returns `unknown` or a model,
the tool can report the obligation that failed, but it cannot tell you what to
change — the search that produced the model is not a diagnosis.

```
$ cat broken.ic
spec transfer(a: int[0..255], b: int[0..255], amount: int[0..255])
  returns (x: int[0..255], y: int[0..255])
  requires amount <= a
  ensures x == a - amount
  ensures y == b + amount
  ensures x + y == a + b
{ x := a - amount; y := b + amount - 1; }

$ probatum check broken.ic
VERDICT: VIOLATED — a concrete counterexample exists:
  input:  a=0, b=0, amount=0
  cause:  result `y` = -1 outside declared int[0..255]
  suggested fix:
    - `y` produced -1, outside int[0..255]. Either widen the result
      declaration, or add a `requires` that keeps the value inside it
```

Three things happened at once, and each is a deliberate design choice:

1. **The witness is minimal.** `a=0, b=0, amount=0` — not `a=255, b=0,
   amount=255`, which is what an unminimized symbolic model looked like during
   development. Minimization is two-phase (strict coordinate descent, then
   coordinated probes) because coordinate descent alone cannot leave `(0,6)`
   when `(3,3)` is strictly better.
2. **A failing comparison is reported numerically.** The evaluator is re-run at
   the minimal input and both sides are printed:

   ```
   cause:  ensures #2 false: (y == (b + amount)) — the program has 0 where
           the contract needs 1 (short by 1)
   ```
3. **The advice names the construct.** Not "verify your invariants" — the
   `requires` to add, the declaration to widen, or the loop state where
   induction breaks. And when an obligation fails, the *conjunct that broke* is
   evaluated and named, rather than printed as part of a conjunction for you to
   search:

   ```
   $ probatum check bad_invariant.ic
   VERDICT: VIOLATED — a concrete counterexample exists:
     input:  n=0, i=0, acc=0
     cause:  loop preservation fails: ((acc + i) == sum(k in 0..(i + 1): k))
             is not established at this state
     suggested fix:
       - the invariant is not inductive: it holds at [n=0, i=0, acc=0], but the
         body does not restore it. Strengthen it with the fact the body
         changes — normally a statement about the counter, the accumulator,
         or how much of the array has been consumed
   ```

   The spec that produces that output is `acc == sum(k in 0..i: k)` where the
   body needs `sum(k in 0..i-1: k)` — an off-by-one in the invariant, the most
   common loop-proof mistake there is.

Reproduce: `probatum check` on any spec in `examples/` after breaking it. The
diagnosis tests are `minimizes_the_counterexample`,
`advice_names_the_construct_to_change` and
`diagnosis_reports_the_values_on_both_sides` in `src/prove.rs`.

---

## Axis 2: time to first proof

```
$ cargo install probatum
$ probatum examples && probatum check examples/transfer_funds.ic
```

That is the whole setup. There is no solver to install, no version of Z3 to
match, no toolchain to pin. The cost is that the fragment is small — see the
lost axes above.

Why this matters more than it sounds: the reason most developers never try a
verifier is not that they cannot, it is that the first hour is spent on
plumbing instead of on a proof. Compare that to installing a specific Rust
nightly *and* a matching Z3 before a single line is verified.

Reproduce: on a machine without Rust, time `cargo install probatum` to the
first `PROVED`. Ours: a fresh install compiles in well under a minute, and the
binary has no runtime dependencies at all.

---

## Axis 3: the trust surface

`probatum 0.1.0`, as published: **8,924 lines of Rust across 13 files, zero
dependencies** (crates.io reports the line count from the published tarball).

Everything that makes a verdict is in those lines: the parser, the reference
evaluator that defines the semantics, the ROBDD engine, the bit-blaster
including division circuits, the Hoare-logic condition generator, and a
hand-written SHA-256. There is no solver, no SMT-LIB, no `unsafe`.

Two consequences the established tools cannot offer:

- **Nothing to trust but the source.** With an SMT-backed tool the answer is
  only as good as a large solver's soundness; here the check is a boolean
  function you could in principle evaluate by hand.
- **The proof is re-derived, not replayed.** `probatum verify` reads the spec
  and the certificate and re-runs the engines from scratch, byte-comparing the
  result. Two *independent* engines must agree, and a disagreement is reported
  as an internal error rather than resolved by picking a winner. That policy
  caught four bugs in probatum's own proof code during development.

Reproduce: `wc -l src/*.rs`, `cat Cargo.toml` (the `[dependencies]` section is
empty), then `probatum verify <cert> <spec>`.

---

## What probatum does not claim

- **It is not a better verifier of Rust code.** Verus and Kani verify programs
  you already wrote. probatum verifies a small language that it compiles to
  Rust. That is a real limitation, not a framing trick.
- **It cannot prove mathematics.** Lean 4 is an interactive theorem prover with
  dependent types and decades of library work. probatum decides bounded
  arithmetic contracts.
- **Bounded domains are a real restriction.** `int[0..255]` is not `int`. The
  compensation is that the answer is complete inside the domain instead of
  "solver said unknown" — but if your values are genuinely unbounded, use
  Dafny.
- **No recursion, no heap, no dynamic allocation, no floats.** Decimals are
  exact fixed point, which is what money is; binary floating point is not
  modelled at all, deliberately.
- **Four bugs in this codebase were caught by its own cross-validation, not by
  its test suite.** They are documented in [`ARCHITECTURE.md`](ARCHITECTURE.md).
  Read that section before trusting a `PROVED` on your own spec — it tells you
  exactly which failure modes this design catches and how.

---

## How to check us, in three commands

```console
$ cargo install probatum
$ probatum examples && probatum check examples/transfer_funds.ic   # a proof
$ probatum check broken.ic                                        # a diagnosis
```

If the diagnosis is not visibly better than what your current tool prints when
a proof fails, this project has no reason to exist and you should keep using
what you have.
