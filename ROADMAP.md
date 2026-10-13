# Roadmap

Where `ic` is, and where it's going. Ordered by what makes proofs *more complete
and more useful*, not by what's impressive in a demo.

## Now (v0.1) — shipped

- [x] Intent language: bounded `int[lo..hi]`, `requires`/`ensures`/`invariant`/`example`, optional body
- [x] Reference evaluator as the single semantics
- [x] Exhaustive engine (complete within budget)
- [x] BDD-symbolic engine (complete within node budget), interleaved Bryant ordering
- [x] **Cross-validation**: independent engines must agree or we refuse to certify
- [x] Vacuity check (refuses to "prove" an unreachable contract)
- [x] Statistical engine with Clopper–Pearson bound — never claims proof
- [x] SHA-256-sealed certificates; tamper detection; independent `ic verify`
- [x] CEGIS synthesizer: definitional + piecewise extraction, typed enumeration, counterexample refinement
- [x] Codegen: Rust, Go, DSL
- [x] 7 bundled examples, 63 tests (unit + integration)

## Next — completeness of the two engines

- [ ] **Division/modulo circuits in the bitblaster.** The BDD engine currently
      *declines* division (honestly, never guessing). A restoring-division
      circuit would make `safe_reciprocal`-class specs cross-validate too.
- [ ] **`bool` parameters and results across all engines.** The language
      accepts them; the proof engines don't yet. Small width, but it unblocks
      flag/enum-style contracts.
- [ ] **Model counting in reports.** `count_sat` already computes how many
      assignments violate a contract; surface it as "0.03% of the domain is
      bad" in `ic check` output.
- [ ] **Incremental / parallel exhaustive engine.** Chunk the odometer across
      threads; stop at the first violation for `VIOLATED`, or prove in
      parallel. 10–40× on multi-core for the exhaustive path.

## Then — bigger contracts

- [ ] **Arrays with bounded length** and `forall`/`exists` quantifiers over
      them. The single biggest expressiveness jump: sorting, deduplication,
      in-place algorithms. Bitblasting arrays is the hard part (BDD size);
      the exhaustive engine handles them first via bounded enumeration.
- [ ] **Loops with invariants.** A loop is *intent*: `while i < n
      invariant <expr>`. The prover checks the invariant is inductive
      (established on entry, preserved by the body, implies the postcondition
      on exit) — the same proof shape as the exhaustive engine's domain walk,
      but one iteration at a time.
- [ ] **Recursive functions with termination measures.** A `decreases` clause,
      proven to strictly decrease on every recursive call.
- [ ] **Unbounded integers** for a Presburger-arithmetic fragment (+, −,
      comparisons, quantifiers) via a decision procedure, complementing the
      bounded engines. Honest scope: multiplication of two variables is not
      Presburger; `ic` will decline it rather than approximate.
- [ ] **`real`/rational arithmetic** with exact semantics (no floating point
      in the prover; floating point would need its own explicitly-specified
      IEEE model).

## Then — better synthesis

- [ ] **Observational-equivalence pruning across sizes.** Currently dedup is
      per-sort and per-round; a global signature table would prune more.
- [ ] **Component-based synthesis** from a user-extensible library of
      domain operators (saturating arithmetic, bit tricks, statistics
      primitives), so specs can name intent at a higher level.
- [ ] **CEGIS witness completion for coupled multi-result specs.** Today a
      counterexample's valid output tuple is found by bounded enumeration over
      the result domains (capped). A proper constraint solver would lift the cap.
- [ ] **Synthesis hints in the spec.** `ensures` shapes the search; an optional
      `suggest` clause would let a human point the enumerator at a family of
      expressions without writing the body.

## Then — the developer surface

- [ ] **`ic diff`**: show which clause a counterexample violates, in spec terms.
- [ ] **Language server (LSP)**: live clause checking, on-type synthesis
      preview, jump-to-counterexample.
- [ ] **CI action**: `ic check` on every PR, with a stable exit code and a
      diffable certificate artifact.
- [ ] **Certificate chaining across modules.** A function's certificate becomes
      a lemma another spec can `assume` — compositional verification. The
      trust boundary stays auditable because each certificate re-derives
      independently.
- [ ] **Proof-carrying codegen for more targets**: TypeScript, Python
      (with `assert`-based backstops), Zig, C.

## Not planned (and why)

- **Floating-point "proofs" without a specified model.** IEEE-754 semantics are
  subtle (rounding, NaN, signed zero). `ic` will not emit a proof whose
  semantics it has not written down. When `real` arrives it will be exact
  rational, not float.
- **Proving properties of infinite domains by sampling.** Sampling is a
  heuristic and will always be labeled as one. A statistical engine that
  whispered "proved" would destroy the only thing worth having here.
- **Trusting the synthesizer.** Synthesis proposes; the prover disposes. No
  future feature will let a synthesized artifact skip the prover.

---

## Contributing / philosophy

The project is organized around a few rules that are worth more than any single
feature. From [ARCHITECTURE.md](ARCHITECTURE.md#design-rules):

- A declined engine is never a false proof.
- A statistical result is never labeled a proof.
- A vacuous precondition is never "proved".
- On engine disagreement, refuse to certify — never pick a winner.
- The evaluator is the only semantics; the two complete engines share no code.
- Synthesis never trusts itself.

The two engine bugs caught by cross-validation during development (a BDD
cache-key truncation, a circuit-width error) are the argument for taking these
rules seriously: they are exactly the bugs that a system without a safety net
would have shipped.
