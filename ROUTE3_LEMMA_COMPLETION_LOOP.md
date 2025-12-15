# Route 3 lemma-completion loop (copy/paste driver)

## One-line prompt to paste repeatedly

**Prompt:**

> Continue Route 3 lemma completion using `ROUTE3_LEMMA_COMPLETION_LOOP.md`.
> Pick the next unchecked item in the checklist below, implement it in Lean with minimal API churn,
> run `lake build` for the relevant module(s), fix any errors, then update this checklist.
> Don’t ask for confirmation; just keep going until the next item is complete.

## What “done” means

- No `sorry` remains in the targeted declaration(s) (or the targeted obligation is instantiated/proved).
- `lake build` succeeds for the module(s) you touched.

## Priority checklist (edit this file as we go)

### A) Eliminate remaining `sorry` in `HilbertRealization.lean`

- [ ] **`gns_hilbert_realization`**: replace the `sorry` with a real construction/proof.
  - File: `RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean`
  - Notes: This is “mechanical GNS”; should ideally use quotient + completion machinery already in Mathlib.

- [ ] **`caratheodory_positive_definite`**: replace the `sorry` with either (i) an imported Mathlib theorem if it exists, or (ii) a proved lemma in our repo.
  - File: `RiemannRecognitionGeometry/ExplicitFormula/HilbertRealization.lean`
  - Notes: If Mathlib lacks it, we can relocate it to a dedicated file and keep it as an explicit assumption only if absolutely necessary.

### B) Instantiate the Route 3 spectral identity bundle (the “hard blocker wiring”)

- [ ] **Choose concrete `F` and `L : LagariasFramework F`** (if not already fixed) for Route 3.

- [ ] **Provide `Route3SesqIntegralHypBundle` instance** for that `F`/`L`:
  - [ ] `transform_eq_mellinOnCriticalLine`
  - [ ] `weight_nonneg`
  - [ ] `memL2`
  - [ ] `normalization_match` (with abstract weight `w`)
  - [ ] `boundary_limits : w = weightOfJ J`
  - [ ] `fubini_tonelli` (as `Route3FubiniTonelliObligations`)

### C) Expand `Route3FubiniTonelliObligations` into proved lemmas (when B is underway)

This list corresponds to the fields of `Route3FubiniTonelliObligations`.

- [ ] `integrable_integrand`
- [ ] `integrable_integrand₂`
- [ ] `integral_integral_swap`
- [ ] `summable_term₀`
- [ ] `integrable_tsum_term₀`
- [ ] `integral_tsum_term₀`
- [ ] `summable_term₁`
- [ ] `integrable_tsum_term₁`
- [ ] `integral_tsum_term₁`
- [ ] `integrable_trunc`
- [ ] `tendsto_integral_trunc`

## Working rules (keep the loop efficient)

- Prefer using existing Mathlib theorems/structures over rewriting theory from scratch.
- Avoid adding new axioms unless there is a clear Mathlib gap; if you must, isolate them in a small “Assumptions” structure.
- Keep changes localized: one file at a time unless a refactor is forced.
- Always end each iteration by updating the checklist above.
