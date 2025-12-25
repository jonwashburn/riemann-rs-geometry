/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BRF Route: Cayley / Schur Plumbing

Ported from: reality/IndisputableMonolith/NumberTheory/RiemannHypothesis/BRFPlumbing.lean

This file formalizes the **purely algebraic** part of the bounded-real / Schur/Herglotz route
appearing in `Riemann-Christmas.tex`:

- A function `H` is (half-plane) **Herglotz** when `0 ≤ Re H`.
- Its Cayley transform `Θ = (H - 1)/(H + 1)` is **Schur** when `‖Θ‖ ≤ 1`.

The key point for the RH route is that this step is *fully unconditional* and requires
no analytic number theory—only complex algebra.
-/

import Mathlib

namespace RiemannRecognitionGeometry
namespace BRF

open scoped Real

/-!
## Cayley transform: right half-plane → unit disk
-/

/-- The Cayley transform sending the right half-plane to the unit disk:
`cayley H = (H - 1)/(H + 1)`. -/
noncomputable def cayley (H : ℂ) : ℂ :=
  (H - 1) / (H + 1)

theorem normSq_add_one_sub_normSq_sub_one (z : ℂ) :
    Complex.normSq (z + 1) - Complex.normSq (z - 1) = 4 * z.re := by
  -- Expand `normSq` into re/im coordinates.
  simp [Complex.normSq_apply]
  ring

/-- If `Re z ≥ 0`, then the Cayley transform lies in the closed unit disk. -/
theorem norm_cayley_le_one_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    ‖cayley z‖ ≤ 1 := by
  -- `z ≠ -1`, hence `z + 1 ≠ 0`, hence `normSq (z+1) > 0`.
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hzneg : z = (-1 : ℂ) := by
      have : z = -(1 : ℂ) := eq_neg_of_add_eq_zero_left h
      simpa using this
    have : (0 : ℝ) ≤ (-1 : ℂ).re := by simpa [hzneg] using hz
    -- contradiction: `0 ≤ -1`
    have : (0 : ℝ) ≤ (-1 : ℝ) := by simpa using this
    nlinarith
  have hpos : 0 < Complex.normSq (z + 1) :=
    (Complex.normSq_pos).2 hz1

  -- Show `normSq (z-1) ≤ normSq (z+1)` by an explicit identity.
  have hle : Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) := by
    have : 0 ≤ Complex.normSq (z + 1) - Complex.normSq (z - 1) := by
      have : 0 ≤ 4 * z.re := by nlinarith [hz]
      simpa [normSq_add_one_sub_normSq_sub_one z] using this
    exact (sub_nonneg).1 this

  -- Convert `normSq` control into a norm bound via `‖z‖^2 = normSq z`.
  have hnSq : Complex.normSq ((z - 1) / (z + 1)) ≤ 1 := by
    have : Complex.normSq (z - 1) / Complex.normSq (z + 1) ≤ 1 :=
      (div_le_one hpos).2 hle
    simpa [Complex.normSq_div] using this
  have hsq : ‖(z - 1) / (z + 1)‖ ^ 2 ≤ 1 := by
    -- Use `normSq_eq_norm_sq` to relate ‖·‖² and normSq.
    calc
      ‖(z - 1) / (z + 1)‖ ^ 2 = Complex.normSq ((z - 1) / (z + 1)) := by
        rw [← Complex.normSq_eq_norm_sq]
      _ ≤ 1 := hnSq
  have hw : 0 ≤ ‖(z - 1) / (z + 1)‖ := norm_nonneg _
  -- `0 ≤ ‖w‖` and `‖w‖^2 ≤ 1` implies `‖w‖ ≤ 1`.
  have : ‖(z - 1) / (z + 1)‖ ≤ 1 := by nlinarith [hsq, hw]
  simpa [cayley] using this

/-- If the Cayley transform lies in the closed unit disk and `z ≠ -1`,
then `Re z ≥ 0`. -/
theorem re_nonneg_of_norm_cayley_le_one {z : ℂ} (hz : z ≠ (-1 : ℂ))
    (h : ‖cayley z‖ ≤ 1) :
    0 ≤ z.re := by
  have hz1 : z + 1 ≠ 0 := by
    intro h0
    have : z = (-1 : ℂ) := by
      have : z = -(1 : ℂ) := eq_neg_of_add_eq_zero_left h0
      simpa using this
    exact hz this
  have hpos : 0 < Complex.normSq (z + 1) :=
    (Complex.normSq_pos).2 hz1

  -- Square the norm inequality to reach a `normSq` inequality.
  have hnSq_ratio : Complex.normSq ((z - 1) / (z + 1)) ≤ 1 := by
    have hw : 0 ≤ ‖(z - 1) / (z + 1)‖ := norm_nonneg _
    have hsq : ‖(z - 1) / (z + 1)‖ ^ 2 ≤ 1 := by
      have h' : ‖(z - 1) / (z + 1)‖ ≤ 1 := by
        simpa [cayley] using h
      -- `linarith` struggles with squares; `nlinarith` works.
      nlinarith [h', hw]
    -- Convert using `normSq_eq_norm_sq` to relate normSq and ‖·‖².
    calc
      Complex.normSq ((z - 1) / (z + 1))
          = ‖(z - 1) / (z + 1)‖ ^ 2 := by
            rw [Complex.normSq_eq_norm_sq]
      _ ≤ 1 := hsq
  have hratio : Complex.normSq (z - 1) / Complex.normSq (z + 1) ≤ 1 := by
    simpa [Complex.normSq_div] using hnSq_ratio
  have hle : Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) :=
    (div_le_one hpos).1 hratio

  have : 0 ≤ Complex.normSq (z + 1) - Complex.normSq (z - 1) :=
    (sub_nonneg).2 hle
  have : 0 ≤ 4 * z.re := by
    simpa [normSq_add_one_sub_normSq_sub_one z] using this
  nlinarith

/-!
## Paper-compatible `Θ = (2J - 1)/(2J + 1)`
-/

/-- The BRF Cayley transform used in the RH manuscripts: `Θ(J) = (2J-1)/(2J+1)`. -/
noncomputable def theta (J : ℂ) : ℂ :=
  cayley (2 * J)

theorem norm_theta_le_one_of_re_nonneg {J : ℂ} (hJ : 0 ≤ J.re) :
    ‖theta J‖ ≤ 1 := by
  -- `Re (2J) = 2 * Re J`
  have : 0 ≤ (2 * J).re := by
    simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hJ)
  simpa [theta] using (norm_cayley_le_one_of_re_nonneg (z := 2 * J) this)

theorem re_nonneg_of_norm_theta_le_one {J : ℂ} (hJ : 2 * J ≠ (-1 : ℂ))
    (hθ : ‖theta J‖ ≤ 1) :
    0 ≤ J.re := by
  have : 0 ≤ (2 * J).re :=
    re_nonneg_of_norm_cayley_le_one (z := 2 * J) (hz := hJ) (by simpa [theta] using hθ)
  -- Divide by the positive constant `2`.
  have : 0 ≤ (2 : ℝ) * J.re := by simpa using this
  nlinarith

end BRF
end RiemannRecognitionGeometry
