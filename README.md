# probatum

> *probatum* — Latin, "proved" (from *probare*: to test, to try, to prove).
> *Probatum est* was stamped on remedies that had been tested and found true —
> a certification mark. That is what this tool leaves on your code.

**You write the contract. It writes — and proves — the code.**

`probatum` turns *behavioral intent* — preconditions, postconditions, inductive loop
invariants, quantifiers, witnesses — into a working program **plus a
machine-checkable proof certificate** that the program satisfies that intent
for **every** input in its domain. Not the inputs you tested. All of them.

```
$ probatum check examples/sum_to_n.ic

spec: sum_to_n
  engine exhaustive-execution Proved   checked=101
  engine hoare-verification   Proved   checked=105  nodes=52771
    4 verification condition(s): contract, loop entry/preservation/exit, and termination
  cross-validated: two independent complete engines agree
VERDICT: PROVED — every input satisfying `requires` meets every `ensures`
```

That is a **loop** — an infinite family of executions — proved by an inductive
invariant, cross-checked by running the loop on every input in the domain.

---

## Quick start

```console
$ git clone https://github.com/HyperonX-Team/probatum && cd probatum
$ cargo build --release

$ ./target/release/probatum examples          # write the 13 bundled specs
$ ./target/release/probatum check   examples/sum_to_n.ic
$ ./target/release/probatum compile examples/transfer_funds.ic --emit rust,go
$ ./target/release/probatum verify  <out>/transfer_funds.cert <out>/transfer_funds.ic
```

Every command exits `0` on proved/verified, `1` on refuted (with a concrete
counterexample), `2` on inconclusive or usage error — so it drops into CI.

**No dependencies.** Zero external crates: the SHA-256, the CLI parsing, the
BDD engine and the division circuits are all in this repository. A verifier you
cannot audit is a verifier you cannot trust.

---

## What it can do

Each of these is a real spec in [`examples/`(https://github.com/HyperonX-Team/probatum/tree/main/examples), all PROVED.

### Loops, by inductive invariant

A loop is an infinite family of executions; testing it is exactly what does not
work. `probatum` requires an invariant — without one a loop could only be run, never
proved, and it says so.

```
while i <= n
  invariant acc == sum(k in 0..i - 1: k)   // symbolic bound: the whole point
  decreases n - i + 1                      // and this proves termination
{ acc := acc + i; i := i + 1; }
```

Three obligations are generated and discharged: the invariant holds on entry,
is preserved by every iteration, and implies the postcondition when the guard
fails. A fourth proves termination. Without `decreases`, `probatum` reports **partial
correctness explicitly** rather than quietly proving the weaker thing.

### Arrays and lists

An array is not a special theory: it is exactly *N* integer variables, and
`a[i]` with a **symbolic** `i` compiles to an ITE chain over them. That is exact
for fixed-size arrays — which is what makes array reasoning decidable instead
of approximate.

**Out-of-bounds indexing is a fault, not a silent default.** The classic buffer
bug becomes a proof obligation.

### Dynamic length

The array has a fixed capacity; the *used* length is a runtime value. The loop
runs `n` times and the quantifier bound is a variable — no separate feature
was needed, because `sum(k in 0..n-1: a[k])` already means what it says.

### Text

A string is an array of character codes. Not a trick — that is what a string
is, so every string property is an array property, checked by the same
machinery, and the contract quantifies over **all** positions at once:

```
ensures forall i in 0..3: r[i] == s[3 - i]
```

### Exact decimals (money)

`dec<2>` is fixed point: the value is `stored / 10^2`. Unlike binary floating
point this is **exact** — every value is a rational with denominator 100, so
the prover reasons about it with no IEEE-754 model anywhere.

The type system refuses unit errors: comparing money to a bare integer is
rejected, and `dec * dec` is rejected because it would square the scale.

### Large ranges

Two billion values per parameter, 4 × 10¹⁸ states: the enumerating engine
declines *with a reason*, and the symbolic engine proves the contract over all
of them with a 153k-node BDD. Interleaved (Bryant) variable ordering is what
makes wide arithmetic tractable — it took `transfer_funds` from "budget
exceeded at 5M nodes" to 17k nodes.

### And the original: straight-line contracts

Ledger transfers with a **derived** conservation invariant
(`x + y == a + b` is not stated in the body — the prover derives it), clamping,
saturating arithmetic, safe division, threshold logic.

---

## Why you can believe the certificates

Three rules, enforced in code, and they are the whole point:

**1. Two independent engines must agree.** One walks every input and executes
the program. The other bit-blasts the contract into a boolean function and
reasons about the entire domain at once. They share no code — only
[`eval.rs`(https://github.com/HyperonX-Team/probatum/blob/main/src/eval.rs) as their common specification. If they disagree, `probatum`
reports an internal error and **refuses to certify** rather than picking a
winner.

**2. Every counterexample is confirmed by the evaluator** before it is
reported — by *both* paths. A symbolically-encoded bug cannot become a bogus
accusation against your program.

**3. Honest limits are reported, never hidden.** A declined engine is never a
false proof. A sampling result is never called a proof. A vacuously-true
precondition is refused instead of "proved".

### This is not decoration

The safety net caught **four** real bugs in `probatum`'s own proof machinery during
development. None produced a false proof; the net held.

| Bug | Symptom | Found by |
|---|---|---|
| BDD `ite` cache key truncated an operand | engines disagreed on a correct program | cross-validation |
| Circuits sized from the result range only | `sign_extend` assertion on `a+1-1` | integration test |
| `select()` OR-ed both branches' fault signals | a guarded-out out-of-bounds read accused a correct program | counterexample confirmation |
| array substitution skipped quantifier bodies | `forall i: r[i]==…` kept the **old** `r` | a failing spec |

`probatum verify` re-derives the proof from the spec alone and byte-compares against
the certificate. An integration test tampers with one character and asserts
rejection.

---

## The engine ladder

| Engine | How | Complete? |
|---|---|---|
| `exhaustive-execution` | Runs the real machine — loops, arrays and all — on every input | **Yes**, within budget |
| `bdd-symbolic` | Bit-blasts to a boolean function; UNSAT bad-state = proof over the whole domain | **Yes**, within node budget |
| `hoare-verification` | Generates and discharges verification conditions for control flow | **Yes**, within budget |
| `statistical` | Sampling + Clopper–Pearson bound | **No — never claims proof** |

---

## Honest limits

Read these before trusting anything.

- **`dec × dec` is rejected by design.** Multiplying two scaled values squares
  the scale; a silent rounding rule would be a lie. Multiply by a plain int, or
  scale explicitly.
- **Comparing money to a bare integer is a type error** (except `0`, which is
  scale-invariant). `balance >= 5` is ambiguous — five what?
- **Division by wide operands can exhaust the BDD budget.** Restoring-division
  circuits exist and `safe_reciprocal` cross-validates; at 17-bit operands the
  symbolic engine declines honestly and enumeration finishes the job. Division
  is inherently expensive for BDDs — reported, not hidden.
- **Arrays are fixed capacity.** "Dynamic" means the used length is a runtime
  value, not that the array grows.
- **`bool` parameters aren't handled by the proof engines yet** (literals and
  expressions are).
- **No loops without invariants, no recursion, no heap.** Each is a deliberate
  boundary: the fragment is chosen so the engines can be *complete* over it
  rather than approximate over something larger.

---

## What's in the box

| File | What it is |
|---|---|
| [`src/eval.rs`(https://github.com/HyperonX-Team/probatum/blob/main/src/eval.rs) | **The reference evaluator — the single definition of what intent means.** Every engine agrees with it or is wrong. |
| [`src/hoare.rs`(https://github.com/HyperonX-Team/probatum/blob/main/src/hoare.rs) | Verification-condition generation: contract, loop entry/preservation/exit, termination |
| [`src/bdd.rs`(https://github.com/HyperonX-Team/probatum/blob/main/src/bdd.rs) | Reduced Ordered BDDs: unique table, computed cache, `ite`, model counting |
| [`src/bitblast.rs`(https://github.com/HyperonX-Team/probatum/blob/main/src/bitblast.rs) | Circuits: adders, comparators, multipliers, **restoring division**, ITE-chain array access, exact quantifier unrolling |
| [`src/prove.rs`(https://github.com/HyperonX-Team/probatum/blob/main/src/prove.rs) | The prover: engine ladder, cross-validation, vacuity check, certificates |
| [`src/synth.rs`(https://github.com/HyperonX-Team/probatum/blob/main/src/synth.rs) | CEGIS synthesizer: definitional + piecewise extraction, typed enumeration, counterexample refinement |
| [`src/sha256.rs`(https://github.com/HyperonX-Team/probatum/blob/main/src/sha256.rs) | Hand-written SHA-256, FIPS-180-4 test vectors |
| [`SPEC.md`(https://github.com/HyperonX-Team/probatum/blob/main/SPEC.md) | The language reference |
| [`ARCHITECTURE.md`(https://github.com/HyperonX-Team/probatum/blob/main/ARCHITECTURE.md) | How it fits together, and the trust boundary |
| [`ROADMAP.md`(https://github.com/HyperonX-Team/probatum/blob/main/ROADMAP.md) | Where it goes next — and what is deliberately not planned |

**9,674 lines of Rust · 65 tests · 13 examples · 0 dependencies**

```
$ cargo test --release
test result: ok. 56 passed; 0 failed
test result: ok. 9 passed; 0 failed
```

---

## The whole example set

| Spec | Capability | Evidence |
|---|---|---|
| `transfer_funds` | conservation invariant, derived | 5,625,216 inputs, cross-validated |
| `sum_to_n` | loop + invariant + termination | 4 VCs, symbolic bounds |
| `array_sum` | array slice invariant | 4,084,101 array contents |
| `dyn_length` | runtime length | 600,000 inputs, `n` symbolic |
| `reverse_text` | `forall` over string positions | 456,976 inputs |
| `split_bill` | exact decimals | 10,000,100 inputs |
| `big_range` | 4 × 10¹⁸ states | 153,601 BDD nodes |
| `safe_reciprocal` | division, cross-validated | 1,051,638 BDD nodes |
| `clamp`, `max_value`, `saturating_sub`, `weighted_sum`, `consensus` | synthesized from intent | CEGIS |

---

## License

MIT. See [LICENSE(https://github.com/HyperonX-Team/probatum/blob/main/LICENSE).
