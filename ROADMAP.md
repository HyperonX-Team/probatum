# Roadmap

Where `ic` is, and where it's going. Ordered by what makes proofs *more
complete and more useful*, not by what is impressive in a demo.

## Shipped

**v0.1 — straight-line contracts**
- [x] Intent language: bounded `int[lo..hi]`, `requires`/`ensures`/`example`, optional body
- [x] Reference evaluator as the single semantics
- [x] Exhaustive engine; BDD-symbolic engine
- [x] **Cross-validation**: independent engines must agree or we refuse to certify
- [x] Vacuity check; statistical engine that never claims proof
- [x] SHA-256-sealed certificates; tamper detection; independent `ic verify`
- [x] CEGIS synthesizer (definitional + piecewise extraction, typed enumeration)
- [x] Codegen: Rust, Go, DSL

**v0.2 — control flow**
- [x] Statements: assignment, indexed write, `if`/`else`, `while`, `assert`
- [x] Hoare-logic verification conditions: contract, entry, preservation, exit
- [x] Termination via `decreases`, with *partial correctness* reported explicitly when absent
- [x] Symbolic quantifiers (`forall`, `exists`, `sum`) with **symbolic bounds**
- [x] Obligation counterexamples confirmed by the evaluator before reporting
- [x] Free-variable restriction: an obligation quantifies only over what it mentions

**v0.3 — data**
- [x] Fixed-size arrays and lists: indexed read/write, `len`, faulting out-of-bounds
- [x] Symbolic array access as an ITE chain over element variables
- [x] Read-over-write substitution, quantifier bodies included
- [x] Text as arrays of character codes, with `forall` over positions
- [x] Dynamic length: runtime loop bound and runtime quantifier bound
- [x] Exact fixed-point decimals (`dec<S>`), with unit errors as type errors
- [x] Wide ranges (2 × 10⁹ per parameter, 4 × 10¹⁸ states) via interleaved BDD ordering

**v0.4 — the last declined fragment**
- [x] Restoring-division circuits, signed and truncating toward zero
- [x] Division-by-zero and operand faults mirrored from the evaluator

## Next

- [ ] **`dec × dec` with an explicit rounding mode.** Rejected today because it
  squares the scale; the honest fix is a `rounding(nearest|floor|ceil)` clause
  the proof can see, rather than a silent default.
- [ ] **Nested loops with multiple invariants.** Independent invariants per
  loop already work; the interesting case is stronger invariants needed to
  relate an inner loop to an outer one.
- [ ] **`bool` parameters and results across all engines.** The language accepts
  them; the proof engines do not yet. Small width, unblocks flag-style contracts.
- [ ] **Multiple `decreases` measures** for lexicographic termination.
- [ ] **Whole-program verification**: a verified function's certificate becomes
  a lemma another spec can `assume`, so trust composits instead of piling up.
- [ ] **Model counting in reports**: `count_sat` already knows how many
  assignments violate a contract; surface it as "0.03% of the domain is bad".
- [ ] **Parallel exhaustive engine**: chunk the odometer across threads.

## Developer surface

- [ ] `ic diff` — which clause a counterexample violates, in spec terms
- [ ] LSP: live clause checking, jump-to-counterexample
- [ ] CI action with a diffable certificate artifact (a workflow ships today)
- [ ] More codegen targets: TypeScript, Python, Zig, C

## Not planned, deliberately

- **Floating point without a specified model.** IEEE-754 is subtle (rounding,
  NaN, signed zero). `ic` will not emit a proof whose semantics it has not
  written down. Exact fixed point covers the cases where exactness matters.
- **Sampling that calls itself a proof.** The statistical engine exists, is
  labelled, and always exits non-zero. A heuristic that whispered "proved"
  would destroy the only thing worth having here.
- **Trusting the synthesizer.** Synthesis proposes; the prover disposes. No
  future feature lets a synthesized artifact skip the prover.
- **Loops without invariants.** A loop with no invariant can only be run. `ic`
  makes that a parse error rather than a silent downgrade.

---

## Contributing

The rules in [ARCHITECTURE.md](ARCHITECTURE.md#design-rules) matter more than
any single feature:

- A declined engine is never a false proof.
- A statistical result is never labelled a proof.
- A vacuous precondition is never "proved".
- On engine disagreement, refuse to certify — never pick a winner.
- The evaluator is the only semantics; the two complete engines share no code.
- Every counterexample is confirmed by the evaluator before it is reported.

The four bugs the net caught during development are the argument for taking
these seriously: they are exactly the bugs a system without a safety net ships.
