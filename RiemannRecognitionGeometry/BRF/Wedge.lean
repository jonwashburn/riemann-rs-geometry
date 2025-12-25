/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BRF Route: Boundary Wedge → Positivity

Ported from: reality/IndisputableMonolith/NumberTheory/RiemannHypothesis/Wedge.lean

In `Riemann-Christmas.tex`, the load-bearing boundary condition (P+)
asserts that after a unimodular rotation, the boundary phase `w(t)` is confined to a wedge:

`|w(t)| ≤ π·Υ` with `Υ < 1/2` almost everywhere.

This file records the simple but crucial algebraic consequence:

`|w| ≤ π/2  ⇒  Re(exp(i w)) ≥ 0`,

which is the "entry point" for Poisson transport + the Cayley transform.
-/

import RiemannRecognitionGeometry.BRF.Cayley
import RiemannRecognitionGeometry.BRF.Phase
import Mathlib

namespace RiemannRecognitionGeometry
namespace BRF

open scoped Real
open MeasureTheory

theorem re_phase_nonneg_of_abs_le_pi_div_two {w : ℝ} (hw : |w| ≤ Real.pi / 2) :
    0 ≤ (phase w).re := by
  -- `Re(e^{iw}) = cos(w)` and `cos(w) ≥ 0` on `[-π/2, π/2]`.
  have hw' : w ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact abs_le.mp (by simpa [abs_neg] using hw)
  -- `Complex.exp_ofReal_mul_I_re` rewrites the real part into `Real.cos`.
  simpa [phase] using (Real.cos_nonneg_of_mem_Icc hw')

/-- Almost-everywhere version: a wedge bound implies nonnegativity of the real part of the phase. -/
theorem ae_re_phase_nonneg_of_ae_abs_le_pi_mul
    {w : ℝ → ℝ} {Υ : ℝ}
    (hΥ : Υ ≤ (1 / 2 : ℝ))
    (hw : ∀ᵐ t ∂volume, |w t| ≤ Real.pi * Υ) :
    ∀ᵐ t ∂volume, 0 ≤ (phase (w t)).re := by
  have hpi : Real.pi * Υ ≤ Real.pi / 2 := by
    have hpi0 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    -- multiply `Υ ≤ 1/2` by `π ≥ 0`
    have := mul_le_mul_of_nonneg_left hΥ hpi0
    -- `π * (1/2) = π/2`
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  filter_upwards [hw] with t ht
  exact re_phase_nonneg_of_abs_le_pi_div_two (le_trans ht hpi)

/-- If the boundary wedge holds for `w` with parameter `Υ ≤ 1/2`, then the Cayley/BRF transform
`θ(J)=(2J-1)/(2J+1)` is Schur pointwise for the boundary values `J(t)=e^{iw(t)}`. -/
theorem ae_norm_theta_phase_le_one_of_ae_abs_le_pi_mul
    {w : ℝ → ℝ} {Υ : ℝ}
    (hΥ : Υ ≤ (1 / 2 : ℝ))
    (hw : ∀ᵐ t ∂volume, |w t| ≤ Real.pi * Υ) :
    ∀ᵐ t ∂volume, ‖theta (phase (w t))‖ ≤ 1 := by
  -- From the wedge we get `Re(J) ≥ 0`. Then apply the Cayley lemma.
  have hRe : ∀ᵐ t ∂volume, 0 ≤ (phase (w t)).re :=
    ae_re_phase_nonneg_of_ae_abs_le_pi_mul (w := w) (Υ := Υ) hΥ hw
  filter_upwards [hRe] with t ht
  exact norm_theta_le_one_of_re_nonneg (J := phase (w t)) ht

end BRF
end RiemannRecognitionGeometry
