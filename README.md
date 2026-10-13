# `ic` — The Intent Compiler

**You write the contract. It writes — and proves — the code.**

`ic` is a compiler that turns *behavioral intent* (preconditions, postconditions,
invariants, example witnesses) into a working program **plus a machine-checkable
proof certificate** that the program satisfies that intent for **every** input in
its domain — not just the ones you tested.

```
$ ic compile examples/transfer_funds.ic --emit rust,go

ic: proving...
ic: verdict: PROVED
ic:   engine exhaustive           Proved    checked=5625216
ic:   engine bdd-symbolic         Proved    checked=134217728 nodes=17454
ic: ✓ cross-validated: two independent complete engines agree
ic: proved — transfer_funds in "transfer_funds-verified"
ic:   transfer_funds.cert   transfer_funds.rs   transfer_funds.go
```

That `transfer_funds` example encodes one of the oldest ideas in software —
*"money is conserved"* — as an **invariant the prover derives**, not a test you
hope holds:

```
spec transfer_funds(a: int[0..255], b: int[0..255], amount: int[0..255])
  returns (x: int[0..255], y: int[0..255])
  requires amount <= a                 // you can only send what you have
  requires b + amount <= 255           // the ledger can hold it
  ensures  x == a - amount             // sender debited
  ensures  y == b + amount             // receiver credited
  ensures  x + y == a + b              // NOTHING WAS CREATED OR DESTROYED
  example (100, 50, 25) => (75, 75)    // a witness, checked first
{
  x := a - amount;
  y := b + amount;
}
```

No body? `ic` synthesizes one that satisfies the contract, then proves it.

---

## Why this exists

Testing shows a program works on the inputs you thought of. A **proof** shows it
works on all of them. The gap between those two statements is where production
incidents live.

Formal-verification tools have promised this for fifty years, and they mostly
failed developers because they demanded expertise, annotation effort, and trust
in a black box. `ic` is built around three rules:

1. **The spec is the source of truth.** Comments, formatting, file paths —
   none of it is bound into the proof. Change the contract, the certificate
   stops verifying. That's the point.
2. **The verifier does not trust the compiler.** `ic verify` re-derives the
   entire proof from the spec and checks it against the certificate. If
   anything differs — one byte of the spec, one line of the program — it
   refuses. Certificates are SHA-256-sealed; tampering is detected.
3. **The prover does not trust itself.** When two independent proof engines
   (one walks every input, one reasons symbolically about all of them at once)
   reach a verdict, they must *agree*. If they disagree, `ic` reports an
   internal error and refuses to certify rather than pick a winner. This isn't
   decoration: this safety net has caught two real bugs in `ic`'s own engines
   during development (see [ARCHITECTURE](ARCHITECTURE.md#what-the-net-caught)).

---

## Quick start

```console
$ cargo build --release

# Write the bundled examples somewhere
$ ic examples

# Prove a spec that has a body; emit Rust + Go + the DSL form
$ ic compile examples/transfer_funds.ic --emit rust,go

# Synthesize (no body in the file) and prove
$ ic compile examples/max_value.ic

# Prove-or-refute without emitting anything (exit 0 = proved, 1 = violated)
$ ic check examples/clamp.ic

# Independently re-derive a certificate's proof (does NOT trust the compiler)
$ ic verify examples/transfer_funds-verified/transfer_funds.cert \
           examples/transfer_funds-verified/transfer_funds.ic

# Show a certificate's claims
$ ic replay examples/transfer_funds-verified/transfer_funds.cert
```

Every command exits `0` on proved/verified, `1` on refuted (with a concrete
counterexample), `2` on inconclusive or usage error — so it drops into CI.

### A refuted program tells you exactly why

```
$ ic check broken.ic
VERDICT: VIOLATED — a concrete counterexample exists:
  input:  a=0
  cause:  ensures #1 false: (r == (a + 1))
```

Not "some test failed" — *the input, and the clause that broke.*

---

## What "proved" means here (and what it doesn't)

Honesty is the product. Read this before you trust anything.

**Proved means:** for every input in the declared `int[lo..hi]` domains that
satisfies every `requires` clause, the program terminates without fault
(division by zero, overflow, out-of-range result) and satisfies every `ensures`
clause. The proof is complete — not statistical — whenever an engine finished.
The engines are:

| Engine | How | Complete? | Notes |
|---|---|---|---|
| `exhaustive` | Walks every input in the domain | **Yes**, if it terminates within budget | The definition of correctness by construction |
| `bdd-symbolic` | Bit-blasts the contract to a boolean function; asks if any input reaches a "bad state" | **Yes**, within node budget | Reasons about the whole domain in one step; shares no code with exhaustive |
| `statistical` | Random sampling + Clopper–Pearson bound | **No — never claims proof** | Labels itself `NO VIOLATION FOUND (not a proof)` and exits 2 |

- **Bounded domains are a feature, not a limitation.** A proof over
  `int[0..255]` is a real theorem about a real range. `ic` refuses to pretend
  its domains are infinite; what it proves, it proves completely.
- **Division is honestly declined by the BDD engine** (no circuit implemented
  yet — see [ROADMAP](ROADMAP.md)); the exhaustive engine handles it. A
  declined engine is never a false proof.
- **A precondition that can never be true makes every contract vacuously true.**
  `ic` checks for this and *refuses to certify*: "proved nothing" is not "proved
  everything".
- **The generated Rust/Go guards are a backstop, not the proof.** The proof is
  the certificate. Guards catch drift if someone calls the function outside its
  verified envelope.

---

## The spec language, in one screen

```
spec name(a: int[0..255], b: int[0..9])      // bounded integer parameters
  returns (x: int[0..255])                    // result, with its own domain
  requires a > b                              // precondition (inputs outside: out of domain)
  ensures  x == a - b                         // postcondition — must hold for ALL valid inputs
  ensures  x + b == a                         // an invariant reads the same way
  example (10, 3) => (7)                      // a concrete witness (checked FIRST)
{ x := a - b; }                               // the program — omit it and ic writes one
```

Expressions: `+ - * / %`, comparisons, `&& || !`, `if c then a else b`,
`min(a,b)`, `max(a,b)`. Full reference in
[SPEC.md](SPEC.md).

---

## What's in the box

| File | What it is |
|---|---|
| [`src/lexer.rs`](src/lexer.rs) · [`parser.rs`](src/parser.rs) · [`sema.rs`](src/sema.rs) | Frontend: source → typed AST, with name resolution and static checks |
| [`src/eval.rs`](src/eval.rs) | **The reference evaluator — the single definition of what intent means.** Every engine agrees with it or is wrong. |
| [`src/bdd.rs`](src/bdd.rs) | Reduced Ordered BDDs (unique table, computed cache, `ite` primitive, model counting) |
| [`src/bitblast.rs`](src/bitblast.rs) | Two's-complement circuits: adders, comparators, lazy-`ite` fault mirroring |
| [`src/prove.rs`](src/prove.rs) | The prover: engine ladder, **cross-validation**, vacuity check, certificates |
| [`src/synth.rs`](src/synth.rs) | CEGIS synthesizer: definitional + piecewise extraction, typed enumerative search, counterexample-guided refinement |
| [`src/codegen.rs`](src/codegen.rs) | Emitters: verified program → Rust / Go / DSL |
| [`src/main.rs`](src/main.rs) | The `ic` CLI |
| [`examples/`](examples) | 7 runnable specs, from money conservation to a majority-vote circuit |
| [`tests/integration.rs`](tests/integration.rs) | The acceptance criteria, executed: prove-all, cert roundtrip, tamper detection, standalone-rustc compile, honesty checks |

Zero external dependencies — the SHA-256, the CLI parsing, the proof engines
are all here. A verifier you cannot audit is a verifier you cannot trust.

```
63 tests green.  // 56 unit + 7 integration
```

---

## The story of the two bugs

The strongest thing about `ic` isn't that its engines are right — it's that
they *check each other*, and that when they disagree, the tool refuses to
certify instead of guessing. That policy caught two genuine bugs in `ic`'s own
proof machinery:

1. **A BDD cache-key bug.** The memoization key for the `ite` primitive
   truncated one of its three operands, so different `ite` nodes could collide
   and return the wrong subgraph. Caught because the exhaustive engine said
   `Proved` and the BDD engine said `Violated` — a disagreement. Fixed with a
   proper key; never recurred.
2. **A circuit-width bug.** The bitblaster sized arithmetic circuits from the
   *result's* static range alone. In a chain like `a + 1 - 1`, an intermediate
   is wider than the final range, and the circuit tripped its own assertion.
   Caught in integration testing. Fixed: circuits are now at least as wide as
   their widest operand.

Neither would have produced a false proof — the net held. But both would have
produced confusing behavior. The net is why you can believe the certificates.

---

## License

MIT. See [LICENSE](LICENSE).
