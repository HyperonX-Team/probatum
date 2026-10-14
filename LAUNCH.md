# Launch kit

Three posts, one checklist. Don't paste the same text in all three — HN, Reddit
and Discord reward different things, and identical cross-posts get flagged.

Post **Hacker News first**, on a Tuesday–Thursday between 14:00 and 16:00
German time. Then stay in the thread for four hours. An HN post with an absent
author dies; one where the author answers technically tends to compound.

---

## Before you post anything (10 minutes, GitHub UI)

1. **Repo description** — Settings → General → Description:
   > Write the contract, get the proof: an intent compiler with machine-checked certificates. Zero dependencies.

2. **Topics** — same page, the gear next to "Topics":
   ```
   formal-verification  rust  verification  proof  static-analysis  developer-tools
   ```

3. **Record the 10-second proof.** This is your actual advertisement — not the
   prose. Nobody installs a Rust tool from a paragraph; they install it because
   they saw the counterexample moment. Have a terminal recording or GIF ready:

   ```
   $ probatum check broken.ic
   VERDICT: VIOLATED — a concrete counterexample exists:
     input:  a=0
     cause:  ensures #1 false: (r == (a + 1))
   ```

   Wrong code in, the exact input out. That frame is the whole pitch.

---

## 1. Hacker News

**Title:**

```
Show HN: Probatum – write what your code must do, get a machine-checked proof
```

**First comment (post it immediately after submitting):**

```
Author here. I kept shipping arithmetic bugs that tests didn't catch — an
off-by-one at a boundary, a rounding slip, an overflow in a ledger. Tests check
the inputs you thought of.

Probatum takes the other approach. You write the contract — preconditions,
postconditions, loop invariants, a couple of witnesses — and it either writes
the program for you or proves the one you wrote satisfies that contract for
every input in the declared domain. Then it emits a certificate someone else can
re-verify without trusting the compiler.

What makes the result worth believing:

1. Two complete engines that share no code. One enumerates the domain and
   executes the program; the other bit-blasts the contract into a boolean
   function and reasons about the whole domain at once. If they disagree it
   refuses to certify rather than picking a winner. That policy caught four
   real bugs in my own proof machinery during development.
2. Every counterexample is confirmed by the reference evaluator before it is
   reported, so an encoding bug can't turn into a false accusation against
   your program.
3. No external solver. No SMT, no Z3, zero dependencies. Bounded domains make
   the decision complete instead of "solver said unknown".

What it can't do, up front: no unbounded integers, no recursion, no dynamic
allocation, no floating point (decimals are exact fixed point, which is what
money actually is). Arrays are fixed capacity. If you need those, Dafny and
Verus are mature and handle far more programs than this does. probatum is for
arithmetic and control flow over bounded values — money that must be conserved,
a rate limiter's boundary, a clamp, an array slice.

`cargo install probatum`, then `probatum examples` writes 13 specs and all of
them are proved. MIT, ~9k lines, no dependencies.
```

 → "probatum" before posting)*

---

## 2. r/rust

**Title:**

```
Probatum: an intent compiler in pure Rust (zero dependencies) that proves your code for every input
```

**Body:**

```
Finally got this onto crates.io: `cargo install probatum`.

The idea: you write behavioral intent — preconditions, postconditions,
inductive loop invariants, quantifiers, witnesses — and probatum either
synthesizes a program from it, or proves the one you wrote satisfies it for
every input in the declared bounded domain. It then emits a SHA-256-sealed
certificate that `probatum verify` re-derives from the spec alone.

Rust-specific things people here might care about:

- Zero dependencies. The SHA-256, the CLI parsing, the ROBDD engine and the
  bit-blaster (adders, comparators, multipliers, restoring division) are all in
  the crate. A verifier you can't audit isn't worth much.
- The ROBDD is a straightforward unique-table + computed-cache implementation
  with `ite` as the only primitive. Interleaved (Bryant) variable ordering took
  the flagship example from "node budget exceeded at 5M" to 17k nodes.
- Quantifiers unroll exactly over the widest range their bounds can take, each
  term guarded — which is what makes symbolic bounds like `sum(k in 0..i-1: a[k])`
  work, and that is what makes array-loop invariants provable.
- Two independent engines must agree or it refuses to certify. That policy
  caught four bugs in my own proof code; two were cases where a correct program
  was being accused of violating its contract.
- Emitted Rust compiles with zero warnings, via a precedence-exact emitter: the
  shipped code has to group exactly like the tree the prover verified. Getting
  there meant a real precedence table, not defensive parentheses everywhere.

Honest limits: bounded integer domains only, no recursion, no heap,
fixed-capacity arrays, no floats. Not competing with Verus or Kani on coverage —
this is for when you want a complete answer over a small domain with no solver
in the loop.

13 examples, all proved: transfer_funds (conservation invariant), sum_to_n
(loop invariant + termination), array_sum, dyn_length, reverse_text,
split_bill (exact decimals), big_range (4×10^18 states, symbolically) and five
synthesized from the contract alone.

https://github.com/HyperonX-Team/probatum
https://crates.io/crates/probatum
```

---

## 3. Discord / German communities

```
🛡️ **probatum ist auf crates.io**

Ein Compiler, der Beweise statt Tests liefert.

Du schreibst, WAS der Code tun soll — Voraussetzungen, Invarianten, Beispiele.
probatum schreibt den Code oder **beweist**, dass deiner stimmt. Für alle
Eingaben. Nicht nur die, an die du gedacht hast.

Und wenn deiner falsch ist:

  VERDICT: VIOLATED — a concrete counterexample exists:
    input:  a=0
    cause:  ensures #1 false: (r == (a + 1))

Die exakte Eingabe, die ihn bricht. Nicht "ein Test ist fehlgeschlagen".

✅ Schleifen bewiesen (induktive Invarianten + Terminierung)
✅ Arrays, Texte, dynamische Längen
✅ exakte Dezimal-Mathematik für Geld (kein Float)
✅ beweist 4×10^18 Zustände auf einmal
✅ erzeugt Rust & Go + fälschungssicheres Zertifikat
✅ 0 Dependencies, 9k Zeilen, MIT

Installation:
  cargo install probatum
  probatum examples
  probatum check examples/transfer_funds.ic

📦 https://crates.io/crates/probatum
💻 https://github.com/HyperonX-Team/probatum
```

---

## Rules that matter

- **Don't say "AI".** In this community that word ends the conversation. There
  is no AI in this tool — it's BDDs, Hoare logic and bit-blasting.
- **Lead with the limits, not the features.** Stating what it can't do earns
  credibility for what it can. Every verification audience tests you on this.
- **Answer the "why not Dafny/Verus?" question before it's asked** — that's
  what the comparison table in the README is for.
- **Don't post the same text in five places.** Post HN, then r/rust with a
  different angle, then Discord. Stagger by a day.
- **Expect 200–500 stars and 20–50 real users** if HN goes well. Dafny has
  ~2.6k stars, Kani ~2.5k, Verus ~1k. That is the size of this field, and 50
  users who write money code are worth more than 5,000 stargazers.
- **The strongest long-term advertising is a story, not an announcement.**
  Run probatum against a real open-source spec, find something real, write it
  up. "How I found X in Y" gets shared; announcements get scrolled past.
