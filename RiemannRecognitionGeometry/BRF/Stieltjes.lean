/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BRF Route: Stieltjes Measure Infrastructure

Ported from: reality/IndisputableMonolith/NumberTheory/RiemannHypothesis/WindowToOscillation.lean (lines 46-132)

Defines the Stieltjes measure for `-w` (antitone phase) and the plateau extraction lemma.
-/

import RiemannRecognitionGeometry.BRF.Oscillation
import Mathlib.MeasureTheory.Measure.Stieltjes

namespace RiemannRecognitionGeometry
namespace BRF

open scoped Real Topology
open MeasureTheory Filter Set
open scoped ENNReal

/-!
## Plateau/mass extraction (B1 bridge)

If `μ` is a measure, `φ ≥ 0` is a window function, and `φ` has a pointwise lower bound `c` on a
set `s`, then bounding `∫ φ dμ` controls `μ(s)`:

`(∀ x∈s, c ≤ φ x)` and `(∫ φ dμ ≤ A)`  ⇒  `μ(s) ≤ A / c`.

This is the Lean version of the "plateau ⇒ mass extraction" step used in the active certificate.
-/

namespace Plateau

theorem measure_le_lintegral_div_of_forall_le_on {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {φ : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcTop : c ≠ ⊤) (hle : ∀ x, x ∈ s → c ≤ φ x) :
    μ s ≤ (∫⁻ x, φ x ∂μ) / c := by
  -- First show `c * μ s ≤ ∫ φ dμ` by integrating the indicator of the constant `c` over `s`.
  have h_ind : s.indicator (fun _ : α => c) ≤ φ := by
    intro x
    by_cases hx : x ∈ s
    · simpa [hx] using hle x hx
    · -- outside `s`, the indicator is `0` and `0 ≤ φ x`.
      simp [hx]
  have hmul : c * μ s ≤ ∫⁻ x, φ x ∂μ := by
    calc
      c * μ s = ∫⁻ x, s.indicator (fun _ : α => c) x ∂μ := by
        simpa using (lintegral_indicator_const (μ := μ) hs c).symm
      _ ≤ ∫⁻ x, φ x ∂μ := lintegral_mono h_ind
  -- Divide by `c` using `ENNReal.le_div_iff_mul_le`.
  have : μ s ≤ (∫⁻ x, φ x ∂μ) / c :=
    (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcTop)).2 (by simpa [mul_comm] using hmul)
  exact this

end Plateau

/-!
## Stieltjes measure for `-w`
-/

/-- The Stieltjes function `t ↦ -w(t)` built from an antitone, right-continuous `w`. -/
noncomputable def stieltjesNeg (w : ℝ → ℝ) (hw : Antitone w)
    (hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x) :
    StieltjesFunction :=
  { toFun := fun x => -w x
    mono' := by
      intro x y hxy
      have : w y ≤ w x := hw hxy
      exact neg_le_neg this
    right_continuous' := by
      intro x
      simpa using (hw_rc x).neg }

namespace stieltjesNeg

variable {w : ℝ → ℝ} {hw : Antitone w} {hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x}

/-- The Stieltjes measure associated to `t ↦ -w(t)`. -/
noncomputable def μ : Measure ℝ :=
  (stieltjesNeg w hw hw_rc).measure

lemma leftLim_neg_eq_neg_leftLim (w : ℝ → ℝ) (hw : Antitone w) (b : ℝ) :
    Function.leftLim (fun x => -w x) b = - Function.leftLim w b := by
  -- Antitone functions have left limits; use uniqueness of limits and continuity of `neg`.
  have hwlim : Tendsto w (𝓝[<] b) (nhds (Function.leftLim w b)) :=
    Antitone.tendsto_leftLim hw b
  have hne : (𝓝[<] b) ≠ (⊥ : Filter ℝ) := by
    haveI : NeBot (𝓝[<] b) := by infer_instance
    exact (neBot_iff.1 (by infer_instance))
  have hwlim' : Tendsto (fun x => -w x) (𝓝[<] b) (nhds (-Function.leftLim w b)) :=
    hwlim.neg
  exact leftLim_eq_of_tendsto (f := fun x => -w x) (a := b) hne hwlim'

/-- Stieltjes mass on `Ioo a b` equals the phase drop `w a - leftLim w b` (as `ofReal`). -/
lemma measure_Ioo_eq_ofReal_drop (a b : ℝ) :
    (μ (w := w) (hw := hw) (hw_rc := hw_rc)) (Set.Ioo a b)
      = ENNReal.ofReal (w a - Function.leftLim w b) := by
  -- Start from the generic Stieltjes formula.
  let g : StieltjesFunction := stieltjesNeg w hw hw_rc
  have hIoo : g.measure (Set.Ioo a b) = ENNReal.ofReal (Function.leftLim g b - g a) := by
    simpa using (StieltjesFunction.measure_Ioo (f := g) (a := a) (b := b))
  -- Rewrite `g a = -w a` and `leftLim g b = - leftLim w b`.
  have hLL : Function.leftLim g b = - Function.leftLim w b := by
    -- `g = fun x ↦ -w x`
    simpa [g, stieltjesNeg] using (leftLim_neg_eq_neg_leftLim (w := w) hw b)
  -- Simplify the real expression.
  have : (Function.leftLim g b - g a) = (w a - Function.leftLim w b) := by
    have hga : g a = -w a := by
      simp [g, stieltjesNeg]
    calc
      Function.leftLim g b - g a = Function.leftLim g b - (-w a) := by simpa [hga]
      _ = (-Function.leftLim w b) - (-w a) := by simpa [hLL]
      _ = w a - Function.leftLim w b := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Finish.
  simpa [μ, g, hIoo, this]

end stieltjesNeg

end BRF
end RiemannRecognitionGeometry
