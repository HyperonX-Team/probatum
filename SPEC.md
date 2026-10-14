# The Intent Language — Reference

A spec declares a **contract**: what must be true before (`requires`), what must
be true after (`ensures` / `invariant`), and concrete witnesses (`example`). A
**body** is a straight-line program satisfying it — written by you, or
synthesized by `probatum`.

File extension: `.ic`. Comments: `// line` and `/* block /* nested */ */`.

---

## Structure

```
spec NAME ( PARAMS )
  returns ( RESULTS )
  requires EXPR
  ensures  EXPR
  invariant EXPR          // alias for ensures; reads better on loop-like contracts
  example ( INPUTS ) => ( OUTPUTS )
{                         // optional body — omit it and ic synthesizes one
  RESULT := EXPR ;
  ...
}
```

### Parameters and results

```
a: int[0..255]     // bounded integer: every value in [lo, hi]
v: int[-100..100]  // signed ranges are fine
flag: bool         // declared but not yet supported by the engines (v0.1)
```

**Bounded domains are the point, not a limitation.** A proof over `int[0..255]`
is a real theorem about a real range. `probatum` refuses to pretend its domains are
infinite; what it proves, it proves completely.

Parameter names and result names must be **distinct** — a result named `x` may
not shadow a parameter named `x`, because `x` would then mean two different
things in `requires` versus `ensures`.

### Clauses

- **`requires EXPR`** — precondition. Inputs that violate it are **out of
  domain**: the contract says nothing about them, and `probatum` neither proves nor
  refutes behavior there. If *no* input satisfies `requires`, the contract is
  **vacuous** and `probatum` refuses to certify (a vacuous contract "proves" nothing).
- **`ensures EXPR`** / **`invariant EXPR`** — postconditions. Must hold for
  **every** input in the domain that satisfies `requires`. In `ensures`, `x`
  (or `result.x`) refers to the result; bare names refer to parameters unless
  they are results.
- **`example ( INPUTS ) => ( OUTPUTS )`** — a concrete witness, checked
  **before** anything else. `probatum` refuses a spec whose own witness contradicts
  its contract. Inputs must satisfy `requires` and lie in the declared domains;
  outputs must lie in the result domains.

### Body

Straight-line, **one assignment per result**, each result assigned exactly once.
Assignments are sequential: a later assignment may read an earlier result
(`result.x` or bare `x` after it is assigned). Reading a result *before* it is
assigned is a semantic error.

```
{
  x := a - amount;
  y := b + amount;
}
```

---

## Types

| Type | Meaning |
|---|---|
| `int[lo..hi]` | Integer, every value in the closed range. `lo` and `hi` are literals (negatives allowed). |
| `bool` | Boolean. Supported in expressions; parameters/results of this type are **not yet supported by the proof engines** (see ROADMAP). |
| `array[N] of int[lo..hi]` | Fixed-size array / list. Indices are `0..N-1`; an out-of-range index is a **fault** (a proof obligation, not a silent default). `len(a)` is `N`. Strings are arrays of character codes: `array[4] of int[65..90]` is four letters. |
| `dec<S>[lo..hi]` | Exact fixed-point decimal: the value is `stored / 10^S`. `dec<2>[0..10000]` is 0.00 … 100.00 — cents. Arithmetic is exact; there is no IEEE-754 model anywhere in the prover. |

---

## Statements

```
x := e;                 // assignment
a[i] := e;              // indexed write (i may be symbolic)
assert E;               // inline proof obligation
if C { … } else { … }   // branch
while C invariant I …   // loop — the invariant IS the intent
  decreases V
{ … }
```

A `while` loop **requires at least one `invariant`** — without one the loop
could only be run, never proved, and `probatum` says so instead of pretending.

`locals ( i: int[0..100], acc: int[0..5050] )` declares the loop's working
variables. Statically typed, so every variable's domain is known; internally
verified, never exposed to callers.

### How loops are proved

Three obligations per loop, plus a fourth for termination:

| Obligation | Meaning |
|---|---|
| entry | the invariant holds before the loop |
| preservation | `I ∧ guard ⇒ wp(body, I)` — every iteration keeps it |
| exit | `I ∧ ¬guard ⇒ postcondition` |
| termination | with `decreases V`: `V > 0` and `V` strictly decreases |

Preservation + exit give **partial correctness**. Adding `decreases` gives
**total correctness**. Without it `probatum` reports partial correctness explicitly
rather than quietly proving the weaker thing.

### Quantifiers and folds

```
forall i in 0..n: E      // true for every i
exists i in 0..n: E      // true for some i
sum(k in 0..i-1: a[k])   // fold — the workhorse of array intent
```

Bounds may be **symbolic**: `sum(k in 0..i-1: a[k])` inside a loop invariant
is exactly what makes array loops provable. The symbolic engine unrolls the
quantifier over the widest range its bound can take and guards each term, so
the unrolling is exact rather than approximate.

---

## Types (detailed)

Static analysis computes the **exact interval** of every expression from the
declared domains and uses it to size proof circuits and reject impossible
assignments:

- **Disjoint ranges are rejected statically.** If the expression's range and
  the result's declared range share no value, no input can make it fit — `probatum`
  says so before running anything.
- **Overlapping ranges are deferred to the prover.** Plain interval analysis
  cannot see that `a - amount >= 0` under `requires amount <= a`. That's a
  theorem, not an interval — the proof engines decide, and if no precondition
  saves it, they return a concrete counterexample.

---

## Expressions

Precedence, loosest to tightest:

```
||                      logical or        (short-circuits)
&&                      logical and       (short-circuits)
==  !=  <  <=  >  >=    comparisons
+  -                    additive
*  /  %                 multiplicative
-  !                    unary negation / not
```

| Form | Example | Notes |
|---|---|---|
| Literals | `42`, `-1`, `true`, `false` | |
| Parameters | `a`, `amount` | |
| Results (in `ensures`) | `x`, `result.x` | `result.x` is explicit; bare `x` works and resolves to the result unless it is a parameter |
| Arithmetic | `a + b`, `a - amount`, `2 * a` | i64 semantics; overflow is a **fault**, counted as a violation |
| Division | `a / b`, `a % b` | **Truncates toward zero** — exactly matches Rust and Go codegen. Division by zero is a **fault**. |
| Comparisons | `a <= b`, `x == a - amount` | |
| Boolean | `a > 0 && b > 0`, `!(a == b)` | `&&`/`||` short-circuit — the right side is not evaluated when the left decides |
| Conditional | `if c then a else b` | **Lazy**: the untaken branch is not evaluated, so `if b == 0 then 0 else a / b` is safe by construction |
| `min` / `max` | `min(a, b)`, `max(a - b, 0)` | Builtin; the synthesizer's grammar includes them |

### Faults are violations

The evaluator treats a fault — division by zero, i64 overflow, a result outside
its declared domain — as a **contract violation**, not a crash to be ignored. A
program that faults on a valid input has broken its contract. This is how
`probatum` catches the classic "works until b = 0".

---

## What a spec can and cannot express (v0.1)

**Can:** contracts over bounded integers — preconditions, postconditions,
invariants relating any number of inputs and outputs; concrete witnesses;
straight-line programs using arithmetic, comparison, boolean logic, lazy
conditionals, `min`/`max`.

**Cannot yet:** loops and recursion (see ROADMAP); arrays, strings, tuples;
unbounded integers; `bool` parameters/results in the proof engines; functions
calling other functions; floating point. Each is a planned extension, not a
theoretical limit — the current fragment is chosen so that the two proof engines
can be **complete** over it rather than approximate over something larger.

---

## Worked example, annotated

```
spec transfer_funds(a: int[0..255], b: int[0..255], amount: int[0..255])
  returns (x: int[0..255], y: int[0..255])

  // Out-of-domain, not violated: you cannot send what you do not have,
  // and the ledger cannot hold what does not fit.
  requires amount <= a
  requires b + amount <= 255

  // The two definitional clauses hand the synthesizer its assignment.
  ensures  x == a - amount
  ensures  y == b + amount

  // THE INVARIANT. Nothing here states this in the body — the prover
  // DERIVES it from the two clauses above plus the preconditions.
  ensures  x + y == a + b

  // A witness, checked before anything else runs.
  example (100, 50, 25) => (75, 75)

{
  x := a - amount;
  y := b + amount;
}
```

Omit the body and `probatum` produces exactly these two assignments by definitional
extraction, then proves the conservation invariant for **all 5,625,216**
in-domain inputs — cross-validated by the BDD engine over the entire encoded
domain at once.

---

## Diagnostics you should expect

| Message | Meaning | What to do |
|---|---|---|
| `example #N violates ensures #M` | The spec's own witness contradicts its contract | Fix the spec — `probatum` will not synthesize against a broken contract |
| `example input #N outside declared domain` | Witness out of range | Fix the example or widen the domain |
| `expression ranges over X which is disjoint from declared Y` | No input can make the assignment fit | Fix the assignment or the result's domain |
| `IMPOSSIBLE SPEC: at input (...) no output tuple satisfies every ensures` | Genuine unrealizability proof about the spec | Fix the spec — this is not a synthesis failure |
| `no expression of size ≤ N found ... this is a search bound, not a proof of impossibility` | The enumerator's bound was hit | Add an example to pin the shape, or write the body yourself |
| `precondition is UNSATISFIABLE (vacuous)` | Nothing reaches the body | Fix `requires` — `probatum` will not certify a vacuous contract |
| `ENGINES DISAGREE` | Internal error; two independent engines reached different verdicts | Please report — `probatum` refuses to certify rather than guess |
