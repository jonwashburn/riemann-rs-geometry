/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BRF Route: Essential Oscillation

Ported from: reality/IndisputableMonolith/NumberTheory/RiemannHypothesis/LocalToGlobalWedge.lean (lines 34-56)

Defines essential oscillation of a function on a set with respect to Lebesgue measure.
-/

import Mathlib

namespace RiemannRecognitionGeometry
namespace BRF

open scoped Real
open MeasureTheory Filter

/-!
## Essential oscillation on a set
-/

/-- Essential oscillation of `w` on a set `s`, with respect to Lebesgue measure:
`oscOn w s = essSup(w|_s) - essInf(w|_s)`. -/
noncomputable def oscOn (w : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  essSup w (volume.restrict s) - essInf w (volume.restrict s)

lemma essInf_le_essSup_of_neZero {w : ℝ → ℝ} {μ : Measure ℝ} (hμ : μ ≠ 0)
    (hupper : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) (ae μ) w)
    (hlower : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) (ae μ) w) :
    essInf w μ ≤ essSup w μ := by
  have hae :
      (∀ᵐ x ∂μ, essInf w μ ≤ essSup w μ) := by
    -- combine the pointwise a.e. bounds `essInf ≤ w ≤ essSup`.
    filter_upwards [ae_essInf_le (μ := μ) (f := w) hlower,
      ae_le_essSup (μ := μ) (f := w) hupper] with x hx1 hx2
    exact le_trans hx1 hx2
  by_contra h
  have : μ Set.univ = 0 := by
    -- If the constant inequality is false, its negation holds everywhere; but `hae` says its
    -- negation has measure zero.
    have : μ {x : ℝ | ¬ (essInf w μ ≤ essSup w μ)} = 0 := by
      simpa [MeasureTheory.ae_iff] using hae
    simpa [h] using this
  exact hμ ((Measure.measure_univ_eq_zero).1 this)

end BRF
end RiemannRecognitionGeometry
