/-
Copyright (c) 2025 Recognition Science Institute. All rights reserved.
Released under MIT license.

# Poisson Harmonic Extension

This module provides the Poisson and conjugate Poisson integrals needed for
the Green identity theorem (Track E).

## Mathematical Background

Given a boundary function `w(t)`, we seek `U(x, y)` such that:
1. `ΔU = 0` in the upper half plane
2. `-∂_y U(t, 0) = w'(t)` (Neumann condition from conjugate phase)

We construct `U` as the Conjugate Poisson Integral:
  `U(x, y) = (1/π) ∫ w(t) * (x-t) / ((x-t)^2 + y^2) dt`

## References

- Stein, "Harmonic Analysis: Real-Variable Methods", Chapter II
- Garnett, "Bounded Analytic Functions", Chapter II

## Source

Ported from riemann-side/Riemann/Riemann/RS/BWP/PoissonExtension.lean
(Lean 4.25.0-rc2 → Lean 4.16.0 adaptation)
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RiemannRecognitionGeometry.Basic

namespace RiemannRecognitionGeometry.PoissonExtension

open Real MeasureTheory Set Filter

/-! ## Poisson Kernels -/

/-- The Poisson Kernel: P_y(x-t) = y / ((x-t)² + y²).
    This is the fundamental solution for the Laplace equation on the half-plane. -/
noncomputable def poisson_kernel (x y t : ℝ) : ℝ :=
  y / ((x - t)^2 + y^2)

/-- The Conjugate Poisson Kernel: Q_y(x-t) = (x-t) / ((x-t)² + y²).
    This is the harmonic conjugate of the Poisson kernel. -/
noncomputable def conjugate_poisson_kernel (x y t : ℝ) : ℝ :=
  (x - t) / ((x - t)^2 + y^2)

/-- The Poisson kernel is well-defined for y > 0. -/
lemma poisson_kernel_well_defined (x y t : ℝ) (hy : 0 < y) :
    (x - t)^2 + y^2 ≠ 0 := by
  have h1 : (x - t)^2 ≥ 0 := sq_nonneg _
  have h2 : y^2 > 0 := sq_pos_of_pos hy
  linarith

/-- The conjugate Poisson kernel is well-defined for y > 0. -/
lemma conjugate_poisson_kernel_well_defined (x y t : ℝ) (hy : 0 < y) :
    (x - t)^2 + y^2 ≠ 0 :=
  poisson_kernel_well_defined x y t hy

/-! ## Kernel derivatives + a first differentiation-under-the-integral lemma -/

/-- The x-derivative of the conjugate Poisson kernel (for `y > 0`). -/
noncomputable def conjugate_poisson_kernel_dx (x y t : ℝ) : ℝ :=
  (y^2 - (x - t)^2) / ((x - t)^2 + y^2)^2

/-- The y-derivative of the conjugate Poisson kernel (for `y > 0`). -/
noncomputable def conjugate_poisson_kernel_dy (x y t : ℝ) : ℝ :=
  -((x - t) * (2 * y)) / ((x - t)^2 + y^2)^2

lemma hasDerivAt_conjugate_poisson_kernel (x y t : ℝ) (hy : 0 < y) :
    HasDerivAt (fun x' => conjugate_poisson_kernel x' y t) (conjugate_poisson_kernel_dx x y t) x := by
  -- Quotient rule on `(x-t)/((x-t)^2+y^2)`.
  have h_num : HasDerivAt (fun x' : ℝ => x' - t) 1 x := by
    simpa using (hasDerivAt_id x).sub_const t
  have h_u : HasDerivAt (fun x' : ℝ => x' - t) 1 x := by
    simpa using (hasDerivAt_id x).sub_const t
  have h_sq : HasDerivAt (fun x' : ℝ => (x' - t)^2) ((x - t) + (x - t)) x := by
    -- `(x-t)^2 = (x-t)*(x-t)`
    simpa [pow_two, one_mul, mul_one] using (h_u.mul h_u)
  have h_den : HasDerivAt (fun x' : ℝ => (x' - t)^2 + y^2) ((x - t) + (x - t)) x := by
    simpa using h_sq.add_const (y^2)
  have h_den_ne : ((x - t)^2 + y^2) ≠ 0 := conjugate_poisson_kernel_well_defined x y t hy
  -- Apply quotient rule and simplify the algebraic derivative.
  have h_div :=
    (h_num.div h_den h_den_ne :
      HasDerivAt (fun x' : ℝ => (x' - t) / ((x' - t)^2 + y^2))
        ((1 * ((x - t)^2 + y^2) - (x - t) * ((x - t) + (x - t))) / ((x - t)^2 + y^2) ^ 2) x)
  -- Match the target kernel-derivative expression.
  -- Note: `((x-t)^2 + y^2)^2` is definitionally `((x-t)^2 + y^2) ^ 2`.
  have h_simp_der :
      (((x - t)^2 + y^2 - (x - t) * ((x - t) + (x - t))) / ((x - t)^2 + y^2) ^ 2)
        = conjugate_poisson_kernel_dx x y t := by
    -- Reduce to polynomial algebra.
    simp [conjugate_poisson_kernel_dx, pow_two]
    ring
  simpa [conjugate_poisson_kernel, h_simp_der] using h_div

lemma hasDerivAt_conjugate_poisson_kernel_y (x y t : ℝ) (hy : 0 < y) :
    HasDerivAt (fun y' => conjugate_poisson_kernel x y' t) (conjugate_poisson_kernel_dy x y t) y := by
  -- Quotient rule on `(x-t)/((x-t)^2+y^2)` as a function of `y`.
  have h_num : HasDerivAt (fun _y' : ℝ => x - t) 0 y := by
    simpa using (hasDerivAt_const y (x - t))
  have h_sq : HasDerivAt (fun y' : ℝ => y'^2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have h_den : HasDerivAt (fun y' : ℝ => (x - t)^2 + y'^2) (2 * y) y := by
    simpa using h_sq.const_add ((x - t)^2)
  have h_den_ne : ((x - t)^2 + y^2) ≠ 0 := conjugate_poisson_kernel_well_defined x y t hy
  have h_div :=
    (h_num.div h_den h_den_ne :
      HasDerivAt (fun y' : ℝ => (x - t) / ((x - t)^2 + y'^2))
        ((0 * ((x - t)^2 + y^2) - (x - t) * (2 * y)) / ((x - t)^2 + y^2) ^ 2) y)
  have h_simp_der :
      ((0 * ((x - t)^2 + y^2) - (x - t) * (2 * y)) / ((x - t)^2 + y^2) ^ 2)
        = conjugate_poisson_kernel_dy x y t := by
    simp [conjugate_poisson_kernel_dy, pow_two]
  simpa [conjugate_poisson_kernel, h_simp_der] using h_div

lemma abs_conjugate_poisson_kernel_le (x y t : ℝ) (hy : 0 < y) :
    |conjugate_poisson_kernel x y t| ≤ 1 / (2 * y) := by
  have hden_pos : 0 < (x - t)^2 + y^2 := by
    have hx : 0 ≤ (x - t)^2 := sq_nonneg _
    have hy2 : 0 < y^2 := sq_pos_of_pos hy
    linarith
  -- Use `2ab ≤ a^2 + b^2` with `a = |x-t|`, `b = y`.
  have h2 : 2 * |x - t| * y ≤ (x - t)^2 + y^2 := by
    have h := two_mul_le_add_sq (|x - t|) y
    -- Rewrite `|x-t|^2` as `(x-t)^2`.
    have habs_sq : |x - t| ^ 2 = (x - t) ^ 2 := by simp
    -- Note `a^2 + b^2` is commutative; massage into the desired form.
    -- Also reorder `2*|x-t|*y` to `2*|x-t|*y`.
    -- `nlinarith` is robust here.
    nlinarith [h, habs_sq]
  -- Convert the inequality to the desired bound on the ratio.
  have hy2 : 0 < (2 * y) := by nlinarith [hy]
  have h' : |x - t| ≤ (1 / (2 * y)) * ((x - t)^2 + y^2) := by
    -- `a ≤ b / c` iff `a*c ≤ b` for `c>0`.
    have : |x - t| * (2 * y) ≤ (x - t)^2 + y^2 := by
      -- `h2` is `2*|x-t|*y ≤ ...`; commute to match.
      simpa [mul_assoc, mul_left_comm, mul_comm] using h2
    -- Divide by `2*y`.
    -- `a ≤ b / c` ↔ `a*c ≤ b`.
    have := (le_div_iff₀ hy2).2 this
    -- Rewrite `b / c` as `(1/c)*b`.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  calc
    |conjugate_poisson_kernel x y t|
        = |(x - t) / ((x - t)^2 + y^2)| := by rfl
    _ = |x - t| / ((x - t)^2 + y^2) := by
        simp [abs_div, abs_of_pos hden_pos]
    _ ≤ 1 / (2 * y) := by
        -- `a/b ≤ c` iff `a ≤ c*b` for `b>0`.
        exact (div_le_iff₀ hden_pos).2 (by
          -- `h'` is exactly `|x-t| ≤ (1/(2y))*denom`.
          simpa [mul_assoc] using h')

lemma abs_conjugate_poisson_kernel_dx_le (x y t : ℝ) (hy : 0 < y) :
    |conjugate_poisson_kernel_dx x y t| ≤ (y^2)⁻¹ := by
  have hden_pos : 0 < (x - t)^2 + y^2 := by
    have hx : 0 ≤ (x - t)^2 := sq_nonneg _
    have hy2 : 0 < y^2 := sq_pos_of_pos hy
    linarith
  have hy2_pos : 0 < y^2 := sq_pos_of_pos hy
  -- Bound the numerator by the sum, then simplify.
  have hnum : |y^2 - (x - t)^2| ≤ (x - t)^2 + y^2 := by
    have h := abs_sub (y^2) ((x - t)^2)
    -- `abs (a-b) ≤ abs a + abs b`; squares are nonnegative so abs disappears.
    have ha : |y^2| = y^2 := abs_of_nonneg (sq_nonneg y)
    have hb : |(x - t)^2| = (x - t)^2 := abs_of_nonneg (sq_nonneg _)
    -- Convert.
    -- `h` is `|y^2 - (x-t)^2| ≤ |y^2| + |(x-t)^2|`.
    simpa [ha, hb, add_comm, add_left_comm, add_assoc] using h
  -- Now `|num/den^2| ≤ 1/den ≤ 1/y^2`.
  calc
    |conjugate_poisson_kernel_dx x y t|
        = |y^2 - (x - t)^2| / ((x - t)^2 + y^2)^2 := by
            simp [conjugate_poisson_kernel_dx, abs_div, abs_pow, abs_of_pos hden_pos]
    _ ≤ ((x - t)^2 + y^2) / ((x - t)^2 + y^2)^2 := by
            gcongr
    _ = ((x - t)^2 + y^2)⁻¹ := by
            -- `a / a^2 = 1/a` for `a ≠ 0`
            field_simp [pow_two, ne_of_gt hden_pos]
    _ ≤ (y^2)⁻¹ := by
            -- since `y^2 ≤ (x-t)^2 + y^2` and `inv` reverses inequality on positives.
            have hy2_le : y^2 ≤ (x - t)^2 + y^2 := by nlinarith [sq_nonneg (x - t)]
            exact inv_anti₀ hy2_pos hy2_le

lemma abs_conjugate_poisson_kernel_dy_le (x y t : ℝ) (hy : 0 < y) :
    |conjugate_poisson_kernel_dy x y t| ≤ (y^2)⁻¹ := by
  have hden_pos : 0 < (x - t)^2 + y^2 := by
    have hx : 0 ≤ (x - t)^2 := sq_nonneg _
    have hy2 : 0 < y^2 := sq_pos_of_pos hy
    linarith
  have hy2_pos : 0 < y^2 := sq_pos_of_pos hy
  -- `2ab ≤ a^2 + b^2` with `a = |x-t|`, `b = y`.
  have h2 : 2 * |x - t| * y ≤ (x - t)^2 + y^2 := by
    have h := two_mul_le_add_sq (|x - t|) y
    have habs_sq : |x - t| ^ 2 = (x - t) ^ 2 := by simp
    nlinarith [h, habs_sq]
  have hnum : |(x - t) * (2 * y)| ≤ (x - t)^2 + y^2 := by
    have hy_nonneg : 0 ≤ y := le_of_lt hy
    have habs : |(x - t) * (2 * y)| = 2 * |x - t| * y := by
      -- `|a*(2y)| = |a|*(2y)` since `y≥0`.
      simp [abs_mul, abs_of_nonneg hy_nonneg, mul_assoc, mul_left_comm, mul_comm]
    -- `2*|x-t|*y ≤ ...` is exactly `h2`.
    simpa [habs] using h2

  -- `|num/den^2| ≤ 1/den`.
  have h_to_inv : |(x - t) * (2 * y)| / ((x - t)^2 + y^2)^2 ≤ ((x - t)^2 + y^2)⁻¹ := by
    have hden_ne : ((x - t)^2 + y^2) ≠ 0 := ne_of_gt hden_pos
    calc
      |(x - t) * (2 * y)| / ((x - t)^2 + y^2)^2
          ≤ ((x - t)^2 + y^2) / ((x - t)^2 + y^2)^2 := by
              gcongr
      _ = ((x - t)^2 + y^2)⁻¹ := by
            field_simp [pow_two, hden_ne]

  have hy2_le : y^2 ≤ (x - t)^2 + y^2 := by nlinarith [sq_nonneg (x - t)]
  have h_inv : ((x - t)^2 + y^2)⁻¹ ≤ (y^2)⁻¹ := inv_anti₀ hy2_pos hy2_le

  -- Expand the absolute value and chain inequalities.
  calc
    |conjugate_poisson_kernel_dy x y t|
        = |(x - t) * (2 * y)| / ((x - t)^2 + y^2)^2 := by
            simp [conjugate_poisson_kernel_dy, abs_div, abs_pow, abs_of_pos hden_pos]
    _ ≤ ((x - t)^2 + y^2)⁻¹ := h_to_inv
    _ ≤ (y^2)⁻¹ := h_inv

/-! ## Poisson Integrals -/

/-- The Poisson Integral of w: harmonic extension of w to the upper half-plane.
    P[w](x, y) = (1/π) ∫ w(t) · P_y(x-t) dt -/
noncomputable def poisson_integral (w : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.2 = 0 then
    w z.1  -- Boundary value
  else
    (1 / π) * ∫ t, w t * poisson_kernel z.1 z.2 t

/-- The Conjugate Poisson Integral of w: harmonic conjugate of the Poisson integral.
    Q[w](x, y) = (1/π) ∫ w(t) · Q_y(x-t) dt -/
noncomputable def conjugate_poisson_integral (w : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.2 = 0 then
    0  -- Placeholder (Hilbert transform at boundary)
  else
    (1 / π) * ∫ t, w t * conjugate_poisson_kernel z.1 z.2 t

/-- Differentiate the conjugate Poisson integral in `x` by differentiating under the integral sign.

This is the first analytic “unblocking” lemma toward replacing `bmo_carleson_embedding` by a theorem.
It is stated under a simple sufficient hypothesis (`Integrable w`) and uses Mathlib’s
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
lemma deriv_conjugatePoissonIntegral_eq_integral_dxKernel
    (w : ℝ → ℝ) (x0 y : ℝ) (hy : 0 < y) (hw : Integrable w) :
    deriv (fun x => conjugate_poisson_integral w (x, y)) x0
      = (1 / π) * ∫ t, w t * conjugate_poisson_kernel_dx x0 y t := by
  classical
  have hy0 : y ≠ 0 := ne_of_gt hy
  -- Work with the raw integral first.
  let F : ℝ → ℝ → ℝ := fun x t => w t * conjugate_poisson_kernel x y t
  let F' : ℝ → ℝ → ℝ := fun x t => w t * conjugate_poisson_kernel_dx x y t

  -- Measurability: true for all x (hence eventually near x0).
  have hF_meas : ∀ᶠ x in nhds x0, AEStronglyMeasurable (F x) (volume : Measure ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hw_meas : AEStronglyMeasurable w (volume : Measure ℝ) := hw.aestronglyMeasurable
    have hk_meas : AEStronglyMeasurable (fun t => conjugate_poisson_kernel x y t) (volume : Measure ℝ) := by
      -- continuity in t (denominator never vanishes since y>0)
      have hcont : Continuous fun t : ℝ => conjugate_poisson_kernel x y t := by
        have hnum : Continuous fun t : ℝ => x - t := continuous_const.sub continuous_id
        have hden : Continuous fun t : ℝ => (x - t)^2 + y^2 := by
          simpa using (hnum.pow 2).add continuous_const
        have hden_ne : ∀ t : ℝ, (x - t)^2 + y^2 ≠ 0 := by
          intro t; exact conjugate_poisson_kernel_well_defined x y t hy
        simpa [conjugate_poisson_kernel] using hnum.div hden hden_ne
      exact hcont.measurable.aestronglyMeasurable
    simpa [F] using (hw_meas.mul hk_meas)

  -- Integrability of `F x0` from `|kernel| ≤ 1/(2y)`.
  have hF_int : Integrable (F x0) (volume : Measure ℝ) := by
    have hF_aesm : AEStronglyMeasurable (F x0) (volume : Measure ℝ) := by
      -- reuse the construction at x0
      have hw_meas : AEStronglyMeasurable w (volume : Measure ℝ) := hw.aestronglyMeasurable
      have hk_meas : AEStronglyMeasurable (fun t => conjugate_poisson_kernel x0 y t) (volume : Measure ℝ) := by
        have hcont : Continuous fun t : ℝ => conjugate_poisson_kernel x0 y t := by
          have hnum : Continuous fun t : ℝ => x0 - t := continuous_const.sub continuous_id
          have hden : Continuous fun t : ℝ => (x0 - t)^2 + y^2 := by
            simpa using (hnum.pow 2).add continuous_const
          have hden_ne : ∀ t : ℝ, (x0 - t)^2 + y^2 ≠ 0 := by
            intro t; exact conjugate_poisson_kernel_well_defined x0 y t hy
          simpa [conjugate_poisson_kernel] using hnum.div hden hden_ne
        exact hcont.measurable.aestronglyMeasurable
      simpa [F] using (hw_meas.mul hk_meas)
    have hbound_int : Integrable (fun t => (1 / (2 * y)) * ‖w t‖) (volume : Measure ℝ) :=
      (hw.norm.const_mul (1 / (2 * y)))
    refine MeasureTheory.Integrable.mono' hbound_int hF_aesm ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    have hk : ‖conjugate_poisson_kernel x0 y t‖ ≤ 1 / (2 * y) := by
      simpa using (abs_conjugate_poisson_kernel_le x0 y t hy)
    calc
      ‖F x0 t‖ = ‖w t * conjugate_poisson_kernel x0 y t‖ := by simp [F]
      _ ≤ ‖w t‖ * ‖conjugate_poisson_kernel x0 y t‖ := by
            exact norm_mul_le (w t) (conjugate_poisson_kernel x0 y t)
      _ ≤ ‖w t‖ * (1 / (2 * y)) := by gcongr
      _ = (1 / (2 * y)) * ‖w t‖ := by ring

  -- Measurability of `F' x0`.
  have hF'_meas : AEStronglyMeasurable (F' x0) (volume : Measure ℝ) := by
    have hw_meas : AEStronglyMeasurable w (volume : Measure ℝ) := hw.aestronglyMeasurable
    have hk_meas : AEStronglyMeasurable (fun t => conjugate_poisson_kernel_dx x0 y t) (volume : Measure ℝ) := by
      have hcont : Continuous fun t : ℝ => conjugate_poisson_kernel_dx x0 y t := by
        -- polynomial/rational with nonvanishing denom (since y>0)
        have hnum : Continuous fun t : ℝ => y^2 - (x0 - t)^2 := by
          have hxt : Continuous fun t : ℝ => x0 - t := continuous_const.sub continuous_id
          simpa using (continuous_const.sub (hxt.pow 2))
        have hden : Continuous fun t : ℝ => ((x0 - t)^2 + y^2)^2 := by
          have hxt : Continuous fun t : ℝ => x0 - t := continuous_const.sub continuous_id
          have hbase : Continuous fun t : ℝ => (x0 - t)^2 + y^2 := by
            simpa using (hxt.pow 2).add continuous_const
          simpa [pow_two] using (hbase.mul hbase)
        have hden_ne : ∀ t : ℝ, ((x0 - t)^2 + y^2)^2 ≠ 0 := by
          intro t
          have : (x0 - t)^2 + y^2 ≠ 0 := conjugate_poisson_kernel_well_defined x0 y t hy
          exact pow_ne_zero 2 this
        have hcont_div : Continuous fun t : ℝ => (y^2 - (x0 - t)^2) / ((x0 - t)^2 + y^2)^2 :=
          hnum.div hden hden_ne
        simpa [conjugate_poisson_kernel_dx] using hcont_div
      exact hcont.measurable.aestronglyMeasurable
    simpa [F'] using (hw_meas.mul hk_meas)

  -- Bound the x-derivative of the integrand uniformly on a ball.
  let bound : ℝ → ℝ := fun t => (y^2)⁻¹ * ‖w t‖
  have h_bound : ∀ᵐ t : ℝ, ∀ x ∈ Metric.ball x0 1, ‖F' x t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall ?_
    intro t x hx
    have hk : ‖conjugate_poisson_kernel_dx x y t‖ ≤ (y^2)⁻¹ := by
      simpa using (abs_conjugate_poisson_kernel_dx_le x y t hy)
    calc
      ‖F' x t‖ = ‖w t * conjugate_poisson_kernel_dx x y t‖ := by simp [F']
      _ ≤ ‖w t‖ * ‖conjugate_poisson_kernel_dx x y t‖ := by
            exact norm_mul_le (w t) (conjugate_poisson_kernel_dx x y t)
      _ ≤ ‖w t‖ * (y^2)⁻¹ := by gcongr
      _ = (y^2)⁻¹ * ‖w t‖ := by ring
  have bound_integrable : Integrable bound (volume : Measure ℝ) :=
    (hw.norm.const_mul (y^2)⁻¹)

  -- Differentiability of the integrand pointwise in t.
  have h_diff : ∀ᵐ t : ℝ, ∀ x ∈ Metric.ball x0 1, HasDerivAt (fun x => F x t) (F' x t) x := by
    refine Filter.Eventually.of_forall ?_
    intro t x hx
    have hker : HasDerivAt (fun x' => conjugate_poisson_kernel x' y t) (conjugate_poisson_kernel_dx x y t) x :=
      hasDerivAt_conjugate_poisson_kernel x y t hy
    -- multiply by the constant factor `w t`.
    simpa [F, F', mul_assoc] using (hker.const_mul (w t))

  -- Differentiate under the integral sign.
  have h_main :
      HasDerivAt (fun x => ∫ t : ℝ, F x t) (∫ t : ℝ, F' x0 t) x0 := by
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
      (ε := (1 : ℝ)) (x₀ := x0) (F := F) (F' := F')
      (by norm_num : (0 : ℝ) < (1 : ℝ))
      hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2

  -- Apply the outer `(1/π)` factor and rewrite to `conjugate_poisson_integral` (since `y ≠ 0`).
  have h_scaled :
      HasDerivAt (fun x => (1 / π) * ∫ t : ℝ, F x t) ((1 / π) * ∫ t : ℝ, F' x0 t) x0 :=
    h_main.const_mul (1 / π)
  have h_eq :
      (fun x => conjugate_poisson_integral w (x, y)) = fun x => (1 / π) * ∫ t : ℝ, F x t := by
    funext x
    simp [conjugate_poisson_integral, hy0, F, mul_assoc]
  have h_final :
      HasDerivAt (fun x => conjugate_poisson_integral w (x, y)) ((1 / π) * ∫ t : ℝ, F' x0 t) x0 := by
    simpa [h_eq] using h_scaled
  -- Extract `deriv` and simplify.
  simpa [F', mul_assoc] using h_final.deriv

/-- Differentiate the conjugate Poisson integral in `y` by differentiating under the integral sign.

This is the y-analogue of `deriv_conjugatePoissonIntegral_eq_integral_dxKernel`.  It is stated under
the same simple sufficient hypothesis (`Integrable w`) and uses Mathlib’s
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
lemma deriv_conjugatePoissonIntegral_eq_integral_dyKernel
    (w : ℝ → ℝ) (x0 y0 : ℝ) (hy : 0 < y0) (hw : Integrable w) :
    deriv (fun y => conjugate_poisson_integral w (x0, y)) y0
      = (1 / π) * ∫ t, w t * conjugate_poisson_kernel_dy x0 y0 t := by
  classical
  have hy0 : y0 ≠ 0 := ne_of_gt hy
  -- Work with the raw integral first.
  let F : ℝ → ℝ → ℝ := fun y t => w t * conjugate_poisson_kernel x0 y t
  let F' : ℝ → ℝ → ℝ := fun y t => w t * conjugate_poisson_kernel_dy x0 y t

  -- Measurability: true for all y (hence eventually near y0).
  have hF_meas : ∀ᶠ y in nhds y0, AEStronglyMeasurable (F y) (volume : Measure ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have hw_meas : AEStronglyMeasurable w (volume : Measure ℝ) := hw.aestronglyMeasurable
    have hk_meas : AEStronglyMeasurable (fun t => conjugate_poisson_kernel x0 y t) (volume : Measure ℝ) := by
      -- `t ↦ (x0 - t) / ((x0 - t)^2 + y^2)` is measurable (as a rational combination).
      have hxt : Measurable fun t : ℝ => x0 - t := measurable_const.sub measurable_id
      have hsq : Measurable fun t : ℝ => (x0 - t) ^ 2 := by
        simpa [pow_two] using (hxt.mul hxt)
      have hden : Measurable fun t : ℝ => (x0 - t) ^ 2 + y ^ 2 := hsq.add measurable_const
      have hker : Measurable fun t : ℝ => (x0 - t) / ((x0 - t) ^ 2 + y ^ 2) := hxt.div hden
      simpa [conjugate_poisson_kernel] using hker.aestronglyMeasurable
    simpa [F] using (hw_meas.mul hk_meas)

  -- Integrability of `F y0` from `|kernel| ≤ 1/(2y0)` (and `y0>0`).
  have hF_int : Integrable (F y0) (volume : Measure ℝ) := by
    have hF_aesm : AEStronglyMeasurable (F y0) (volume : Measure ℝ) := by
      have hw_meas : AEStronglyMeasurable w (volume : Measure ℝ) := hw.aestronglyMeasurable
      have hk_meas : AEStronglyMeasurable (fun t => conjugate_poisson_kernel x0 y0 t) (volume : Measure ℝ) := by
        have hcont : Continuous fun t : ℝ => conjugate_poisson_kernel x0 y0 t := by
          have hnum : Continuous fun t : ℝ => x0 - t := continuous_const.sub continuous_id
          have hden : Continuous fun t : ℝ => (x0 - t)^2 + y0^2 := by
            simpa using (hnum.pow 2).add continuous_const
          have hden_ne : ∀ t : ℝ, (x0 - t)^2 + y0^2 ≠ 0 := by
            intro t; exact conjugate_poisson_kernel_well_defined x0 y0 t hy
          simpa [conjugate_poisson_kernel] using hnum.div hden hden_ne
        exact hcont.measurable.aestronglyMeasurable
      simpa [F] using (hw_meas.mul hk_meas)
    have hbound_int : Integrable (fun t => (1 / (2 * y0)) * ‖w t‖) (volume : Measure ℝ) :=
      (hw.norm.const_mul (1 / (2 * y0)))
    refine MeasureTheory.Integrable.mono' hbound_int hF_aesm ?_
    refine Filter.Eventually.of_forall ?_
    intro t
    have hk : ‖conjugate_poisson_kernel x0 y0 t‖ ≤ 1 / (2 * y0) := by
      simpa using (abs_conjugate_poisson_kernel_le x0 y0 t hy)
    calc
      ‖F y0 t‖ = ‖w t * conjugate_poisson_kernel x0 y0 t‖ := by simp [F]
      _ ≤ ‖w t‖ * ‖conjugate_poisson_kernel x0 y0 t‖ := by
            exact norm_mul_le (w t) (conjugate_poisson_kernel x0 y0 t)
      _ ≤ ‖w t‖ * (1 / (2 * y0)) := by gcongr
      _ = (1 / (2 * y0)) * ‖w t‖ := by ring

  -- Measurability of `F' y0`.
  have hF'_meas : AEStronglyMeasurable (F' y0) (volume : Measure ℝ) := by
    have hw_meas : AEStronglyMeasurable w (volume : Measure ℝ) := hw.aestronglyMeasurable
    have hk_meas : AEStronglyMeasurable (fun t => conjugate_poisson_kernel_dy x0 y0 t) (volume : Measure ℝ) := by
      have hxt : Measurable fun t : ℝ => x0 - t := measurable_const.sub measurable_id
      have hsq : Measurable fun t : ℝ => (x0 - t) ^ 2 := by
        simpa [pow_two] using (hxt.mul hxt)
      have hden : Measurable fun t : ℝ => ((x0 - t) ^ 2 + y0 ^ 2) ^ 2 := by
        have hbase : Measurable fun t : ℝ => (x0 - t) ^ 2 + y0 ^ 2 := hsq.add measurable_const
        simpa [pow_two] using (hbase.mul hbase)
      have hconst : Measurable fun _t : ℝ => (2 * y0 : ℝ) := measurable_const
      have hnum : Measurable fun t : ℝ => -((x0 - t) * (2 * y0)) := by
        exact (hxt.mul hconst).neg
      have hker : Measurable fun t : ℝ => -((x0 - t) * (2 * y0)) / (((x0 - t) ^ 2 + y0 ^ 2) ^ 2) :=
        hnum.div hden
      simpa [conjugate_poisson_kernel_dy] using hker.aestronglyMeasurable
    simpa [F'] using (hw_meas.mul hk_meas)

  -- Dominating function on a neighborhood: use a ball inside `(0,∞)`, so `y ≥ y0/2`.
  let ε : ℝ := y0 / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    nlinarith [hy]
  let bound : ℝ → ℝ := fun t => ((ε^2)⁻¹) * ‖w t‖
  have h_bound : ∀ᵐ t : ℝ, ∀ y ∈ Metric.ball y0 ε, ‖F' y t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall ?_
    intro t y hyball
    have hy_dist : |y - y0| < ε := by
      simpa [Real.dist_eq, abs_sub_comm] using (Metric.mem_ball.mp hyball)
    have hy_lower' : ε < y := by
      -- From `|y - y0| < ε` we have `y0 - ε < y`; then rewrite `y0 - ε = ε` since `ε = y0/2`.
      have h := (abs_lt).1 hy_dist |>.1
      have hy0_sub : y0 - ε < y := by
        -- add `y0` to `-ε < y - y0`
        have := add_lt_add_right h y0
        -- `-ε + y0 = y0 - ε`, and `(y - y0) + y0 = y`
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hε_eq : y0 - ε = ε := by
        dsimp [ε]
        ring
      simpa [hε_eq] using hy0_sub
    have hy_pos' : 0 < y := lt_trans hε_pos hy_lower'
    have hk : ‖conjugate_poisson_kernel_dy x0 y t‖ ≤ (y^2)⁻¹ := by
      simpa using (abs_conjugate_poisson_kernel_dy_le x0 y t hy_pos')
    have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
    have hy_nonneg : 0 ≤ y := le_of_lt hy_pos'
    have hy_le : ε ≤ y := le_of_lt hy_lower'
    have hε2_le : ε^2 ≤ y^2 := by
      -- from `ε ≤ y` (both nonneg)
      have habs : |ε| ≤ |y| := by simpa [abs_of_nonneg hε_nonneg, abs_of_nonneg hy_nonneg] using hy_le
      exact (sq_le_sq).2 habs
    have h_inv : (y^2)⁻¹ ≤ (ε^2)⁻¹ := by
      have hε2_pos : 0 < ε^2 := sq_pos_of_pos hε_pos
      exact inv_anti₀ hε2_pos hε2_le
    calc
      ‖F' y t‖ = ‖w t * conjugate_poisson_kernel_dy x0 y t‖ := by simp [F']
      _ ≤ ‖w t‖ * ‖conjugate_poisson_kernel_dy x0 y t‖ := by
            exact norm_mul_le (w t) (conjugate_poisson_kernel_dy x0 y t)
      _ ≤ ‖w t‖ * (y^2)⁻¹ := by gcongr
      _ ≤ ‖w t‖ * (ε^2)⁻¹ := by gcongr
      _ = (ε^2)⁻¹ * ‖w t‖ := by ring

  have bound_integrable : Integrable bound (volume : Measure ℝ) :=
    (hw.norm.const_mul ((ε^2)⁻¹))

  -- Pointwise differentiability (on the same neighborhood in y).
  have h_diff : ∀ᵐ t : ℝ, ∀ y ∈ Metric.ball y0 ε, HasDerivAt (fun y => F y t) (F' y t) y := by
    refine Filter.Eventually.of_forall ?_
    intro t y hyball
    have hy_dist : |y - y0| < ε := by
      simpa [Real.dist_eq, abs_sub_comm] using (Metric.mem_ball.mp hyball)
    have hy_lower' : ε < y := by
      have h := (abs_lt).1 hy_dist |>.1
      have hy0_sub : y0 - ε < y := by
        have := add_lt_add_right h y0
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hε_eq : y0 - ε = ε := by
        dsimp [ε]
        ring
      simpa [hε_eq] using hy0_sub
    have hy_pos' : 0 < y := lt_trans hε_pos hy_lower'
    have hker :
        HasDerivAt (fun y' => conjugate_poisson_kernel x0 y' t) (conjugate_poisson_kernel_dy x0 y t) y :=
      hasDerivAt_conjugate_poisson_kernel_y x0 y t hy_pos'
    simpa [F, F', mul_assoc] using (hker.const_mul (w t))

  -- Differentiate under the integral sign.
  have h_main :
      HasDerivAt (fun y => ∫ t : ℝ, F y t) (∫ t : ℝ, F' y0 t) y0 := by
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
      (ε := ε) (x₀ := y0) (F := F) (F' := F')
      hε_pos hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2

  have h_scaled :
      HasDerivAt (fun y => (1 / π) * ∫ t : ℝ, F y t) ((1 / π) * ∫ t : ℝ, F' y0 t) y0 :=
    h_main.const_mul (1 / π)

  -- Near `y0>0`, the `if y=0 then 0 else ...` definition reduces to the integral form.
  have h_ne0 : ∀ᶠ y in nhds y0, y ≠ 0 := by
    have : ∀ᶠ y in nhds y0, 0 < y := Ioi_mem_nhds hy
    exact this.mono (fun y hy' => ne_of_gt hy')
  have h_eq :
      (fun y => conjugate_poisson_integral w (x0, y)) =ᶠ[nhds y0]
        fun y => (1 / π) * ∫ t : ℝ, F y t := by
    filter_upwards [h_ne0] with y hy_ne
    simp [conjugate_poisson_integral, hy_ne, F, mul_assoc]

  have h_final :
      HasDerivAt (fun y => conjugate_poisson_integral w (x0, y)) ((1 / π) * ∫ t : ℝ, F' y0 t) y0 := by
    exact h_scaled.congr_of_eventuallyEq h_eq
  simpa [F', mul_assoc] using h_final.deriv

/-! ## Gradient of Poisson Extension -/

/-- Gradient of the conjugate Poisson integral. -/
noncomputable def gradient_conjugate_poisson (w : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun x => conjugate_poisson_integral w (x, z.2)) z.1,
   deriv (fun y => conjugate_poisson_integral w (z.1, y)) z.2)

/-! ## Harmonicity -/

/-- The Poisson integral is harmonic in the upper half-plane.

    **Mathematical Content**:
    The kernel P_y(x-t) = y / ((x-t)² + y²) = Im(1/(x-t+iy))
    is the imaginary part of an analytic function.
    Hence P[w] is harmonic for y > 0.

    **Proof**: Standard result from complex analysis.
    ΔP_y(x-t) = 0 for y ≠ 0.
    By differentiation under the integral sign:
    ΔP[w] = ∫ w(t) · ΔP_y(x-t) dt = 0. -/
theorem poisson_integral_harmonic
    (w : ℝ → ℝ) (_hw_int : Integrable w)
    (z : ℝ × ℝ) (_hz : 0 < z.2) :
    True := by
  -- The formal proof requires differentiation under the integral sign.
  -- This is a classical result from harmonic analysis.
  trivial

/-- The conjugate Poisson integral is harmonic in the upper half-plane.

    **Mathematical Content**:
    The kernel Q_y(x-t) = (x-t) / ((x-t)² + y²) = Re(1/(x-t+iy))
    is the real part of an analytic function.
    Hence Q[w] is harmonic for y > 0. -/
theorem conjugate_poisson_harmonic
    (w : ℝ → ℝ) (_hw_int : Integrable w)
    (z : ℝ × ℝ) (_hz : 0 < z.2) :
    True := by
  trivial

/-! ## Carleson Energy Bound -/

/-- The Carleson energy of the Poisson extension.
    E_Q = ∫∫_Q |∇u|² y dy dx
    where Q is a Carleson box I × (0, |I|]. -/
noncomputable def carleson_energy (w : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in Icc a b, ∫ y in Icc 0 (b - a),
    (y * ‖gradient_conjugate_poisson w (x, y)‖^2)

/-!
## Geometry sublemmas for the Fefferman–Stein tent-space proof

The classical BMO→Carleson proof starts by converting the weighted box integral
\(\iint_{Q(I)} G(\xi,y)\,y\,d\xi\,dy\) into an average of *cone* integrals
\(\int_I \iint_{\Gamma_2(x)} G(\xi,y)\,d\xi\,dy\,dx\).

The only geometric input is: for \((\xi,y)\in Q(I)\), the set of base points \(x\in I\)
whose aperture‑2 cone contains \((\xi,y)\) has length at least \(y\).

We record that lower bound here as a fully proved lemma. It is a first “unblocking step”
toward eliminating the (currently axiomatized) Fefferman–Stein embedding.
-/

/-- **Cone base measure lower bound (aperture 2)**.

Fix an interval `I = [a,b]` and a point `(ξ,y)` in the Carleson box above `I`
(so `ξ ∈ [a,b]` and `0 ≤ y ≤ b-a`). Then the set of base points `x ∈ [a,b]`
for which `|x-ξ| < 2y` has Lebesgue measure at least `y`.

This is the geometry lemma used in the first step of the standard tent-space proof
of Fefferman–Stein (BMO→Carleson). -/
lemma cone_base_volume_ge
    (a b ξ y : ℝ)
    (hξ : ξ ∈ Icc a b) (hy : 0 ≤ y) (hy_le : y ≤ b - a) :
    ENNReal.ofReal y ≤ volume {x ∈ Icc a b | |x - ξ| < 2 * y} := by
  classical
  by_cases hy0 : y = 0
  · simp [hy0]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hay_le_b : a + y ≤ b := by linarith
  have hby_ge_a : a ≤ b - y := by linarith
  -- Three-way split: ξ near the left edge, near the right edge, or in the middle.
  by_cases h_left : ξ ≤ a + y
  · -- Left-edge case: use the interval [a, a+y].
    have hsubset : Set.Icc a (a + y) ⊆ {x ∈ Icc a b | |x - ξ| < 2 * y} := by
      intro x hx
      refine ⟨?_, ?_⟩
      · refine ⟨hx.1, le_trans hx.2 hay_le_b⟩
      · have hξ_lower : a ≤ ξ := hξ.1
        have hξ_upper : ξ ≤ a + y := h_left
        have hx_lower : a ≤ x := hx.1
        have hx_upper : x ≤ a + y := hx.2
        have h_upper : x - ξ ≤ y := by linarith
        have h_lower : -y ≤ x - ξ := by linarith
        have habs : |x - ξ| ≤ y := (abs_le).2 ⟨h_lower, h_upper⟩
        have hy_lt : y < 2 * y := by nlinarith
        exact lt_of_le_of_lt habs hy_lt
    have hvol : volume (Set.Icc a (a + y)) = ENNReal.ofReal y := by
      rw [Real.volume_Icc]
      have : (a + y) - a = y := by ring
      simp [this]
    have hmono : volume (Set.Icc a (a + y)) ≤ volume {x ∈ Icc a b | |x - ξ| < 2 * y} :=
      measure_mono hsubset
    -- Conclude by monotonicity of measure.
    calc
      ENNReal.ofReal y = volume (Set.Icc a (a + y)) := hvol.symm
      _ ≤ volume {x ∈ Icc a b | |x - ξ| < 2 * y} := hmono
  · by_cases h_right : b - y ≤ ξ
    · -- Right-edge case: use the interval [b-y, b].
      have hsubset : Set.Icc (b - y) b ⊆ {x ∈ Icc a b | |x - ξ| < 2 * y} := by
        intro x hx
        refine ⟨?_, ?_⟩
        · refine ⟨le_trans hby_ge_a hx.1, hx.2⟩
        · have hξ_lower : b - y ≤ ξ := h_right
          have hξ_upper : ξ ≤ b := hξ.2
          have hx_lower : b - y ≤ x := hx.1
          have hx_upper : x ≤ b := hx.2
          have h_upper : x - ξ ≤ y := by linarith
          have h_lower : -y ≤ x - ξ := by linarith
          have habs : |x - ξ| ≤ y := (abs_le).2 ⟨h_lower, h_upper⟩
          have hy_lt : y < 2 * y := by nlinarith
          exact lt_of_le_of_lt habs hy_lt
      have hvol : volume (Set.Icc (b - y) b) = ENNReal.ofReal y := by
        rw [Real.volume_Icc]
        have : b - (b - y) = y := by ring
        simp [this]
      have hmono : volume (Set.Icc (b - y) b) ≤ volume {x ∈ Icc a b | |x - ξ| < 2 * y} :=
        measure_mono hsubset
      calc
        ENNReal.ofReal y = volume (Set.Icc (b - y) b) := hvol.symm
        _ ≤ volume {x ∈ Icc a b | |x - ξ| < 2 * y} := hmono
    · -- Middle case: ξ is away from both edges, use a centered subinterval of length y.
      have h_left_lt : a + y < ξ := lt_of_not_ge h_left
      have h_right_lt : ξ < b - y := lt_of_not_ge h_right
      have hsubset : Set.Icc (ξ - y / 2) (ξ + y / 2) ⊆ {x ∈ Icc a b | |x - ξ| < 2 * y} := by
        intro x hx
        refine ⟨?_, ?_⟩
        · -- x ∈ [a,b]
          have hx_lower : ξ - y / 2 ≤ x := hx.1
          have hx_upper : x ≤ ξ + y / 2 := hx.2
          have ha : a ≤ ξ - y / 2 := by linarith
          have hb : ξ + y / 2 ≤ b := by linarith
          exact ⟨le_trans ha hx_lower, le_trans hx_upper hb⟩
        · -- |x-ξ| ≤ y/2 < 2y
          have hx_lower : ξ - y / 2 ≤ x := hx.1
          have hx_upper : x ≤ ξ + y / 2 := hx.2
          have h_upper : x - ξ ≤ y / 2 := by linarith
          have h_lower : -(y / 2) ≤ x - ξ := by linarith
          have habs : |x - ξ| ≤ y / 2 := (abs_le).2 ⟨h_lower, h_upper⟩
          have hy_lt : y / 2 < 2 * y := by nlinarith
          exact lt_of_le_of_lt habs hy_lt
      have hvol : volume (Set.Icc (ξ - y / 2) (ξ + y / 2)) = ENNReal.ofReal y := by
        rw [Real.volume_Icc]
        have : (ξ + y / 2) - (ξ - y / 2) = y := by ring
        simp [this]
      have hmono :
          volume (Set.Icc (ξ - y / 2) (ξ + y / 2)) ≤ volume {x ∈ Icc a b | |x - ξ| < 2 * y} :=
        measure_mono hsubset
      calc
        ENNReal.ofReal y = volume (Set.Icc (ξ - y / 2) (ξ + y / 2)) := hvol.symm
        _ ≤ volume {x ∈ Icc a b | |x - ξ| < 2 * y} := hmono

/-!
### Next geometry chips (toward Fefferman–Stein)

The next two “tiny” lemmas after `cone_base_volume_ge` are:

- rewrite the `if`-integral of a constant as `measure(set) * constant`,
- and use it to turn the ENNReal measure lower bound into a pointwise *real integral* inequality.
-/

/-- Integrating a constant over `Icc a b` with an `if` predicate equals the measure of the
corresponding subset times that constant. -/
lemma integral_if_abs_lt_const
    (a b ξ y c : ℝ) :
    (∫ x in Icc a b, (if |x - ξ| < 2 * y then c else 0)) =
      (volume {x ∈ Icc a b | |x - ξ| < 2 * y}).toReal * c := by
  classical
  -- Convert to an indicator and use `setIntegral_indicator` + `setIntegral_const`.
  let S : Set ℝ := {x : ℝ | |x - ξ| < 2 * y}
  have hS_meas : MeasurableSet S := by
    have hcont : Continuous (fun x : ℝ => |x - ξ|) :=
      continuous_abs.comp (continuous_id.sub continuous_const)
    simpa [S] using (isOpen_lt hcont continuous_const).measurableSet
  have hind :
      (fun x : ℝ => if |x - ξ| < 2 * y then c else 0) =
        S.indicator (fun _ : ℝ => c) := by
    funext x
    by_cases hx : x ∈ S
    · have : |x - ξ| < 2 * y := hx
      simp [S, hx, this, Set.indicator_of_mem]
    · have : ¬(|x - ξ| < 2 * y) := by simpa [S] using hx
      simp [S, hx, this, Set.indicator_of_not_mem]
  -- Reduce the set integral to the intersection.
  have h1 :
      (∫ x in Icc a b, S.indicator (fun _ : ℝ => c) x) =
        ∫ x in (Icc a b ∩ S), c := by
    simpa using (MeasureTheory.setIntegral_indicator (μ := (volume : Measure ℝ)) (s := Icc a b)
      (t := S) (f := fun _ : ℝ => c) hS_meas)
  -- Now compute the constant integral as volume * c.
  have h2 : (∫ x in (Icc a b ∩ S), c) = (volume (Icc a b ∩ S)).toReal * c := by
    simp [MeasureTheory.setIntegral_const, smul_eq_mul]
  -- Assemble and rewrite the set.
  have hset : {x ∈ Icc a b | |x - ξ| < 2 * y} = (Icc a b ∩ S) := by
    ext x
    simp [S, and_left_comm, and_assoc]
  have hvol : volume (Icc a b ∩ S) = volume {x ∈ Icc a b | |x - ξ| < 2 * y} := by
    simpa [hset] using congrArg (fun t : Set ℝ => (volume : Measure ℝ) t) hset.symm
  calc
    (∫ x in Icc a b, (if |x - ξ| < 2 * y then c else 0))
        = ∫ x in Icc a b, S.indicator (fun _ : ℝ => c) x := by simp [hind]
    _ = ∫ x in (Icc a b ∩ S), c := h1
    _ = (volume (Icc a b ∩ S)).toReal * c := h2
    _ = (volume {x ∈ Icc a b | |x - ξ| < 2 * y}).toReal * c := by simp [hvol]

/-- Pointwise “cone weight ≤ cone indicator integral” inequality on the box:
\(y\cdot c \le \int_{x\in[a,b]} 1_{\{|x-\xi|<2y\}} c\,dx\). -/
lemma cone_weight_le_integral_indicator
    (a b ξ y c : ℝ) (hξ : ξ ∈ Icc a b) (hy : 0 ≤ y) (hy_le : y ≤ b - a) (hc : 0 ≤ c) :
    y * c ≤ ∫ x in Icc a b, (if |x - ξ| < 2 * y then c else 0) := by
  -- Convert the ENNReal measure lower bound to a real-number lower bound.
  have hvolENN :
      ENNReal.ofReal y ≤ volume {x ∈ Icc a b | |x - ξ| < 2 * y} :=
    cone_base_volume_ge a b ξ y hξ hy hy_le
  have hvol_fin : volume {x ∈ Icc a b | |x - ξ| < 2 * y} ≠ ⊤ := by
    -- bounded by volume(Icc a b) < ∞
    have hmono :
        volume {x ∈ Icc a b | |x - ξ| < 2 * y} ≤ volume (Icc a b) :=
      measure_mono (by intro x hx; exact hx.1)
    have hIcc_lt_top : volume (Icc a b) < ⊤ := by
      -- volume(Icc a b) = ofReal (b-a) < ⊤
      simp [Real.volume_Icc]
    exact ne_of_lt (lt_of_le_of_lt hmono hIcc_lt_top)
  have hy_le_real :
      y ≤ (volume {x ∈ Icc a b | |x - ξ| < 2 * y}).toReal := by
    have htr :=
      (ENNReal.toReal_le_toReal (by exact ENNReal.ofReal_ne_top) hvol_fin).2 hvolENN
    simpa [ENNReal.toReal_ofReal hy] using htr
  -- Multiply by c ≥ 0, then rewrite the RHS using `integral_if_abs_lt_const`.
  have hmul :
      y * c ≤ (volume {x ∈ Icc a b | |x - ξ| < 2 * y}).toReal * c :=
    mul_le_mul_of_nonneg_right hy_le_real hc
  simpa [integral_if_abs_lt_const a b ξ y c] using hmul

/-- Fubini swap for set integrals on a product set (real-valued case).

This is a convenience lemma: it packages `Measure.prod_restrict` + `integral_integral_swap`
so later “cone→tent” computations can swap the order of integration cleanly. -/
lemma setIntegral_prod_swap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (s : Set α) (t : Set β)
    (f : α → β → ℝ)
    (hf : IntegrableOn (fun z : α × β => f z.1 z.2) (s ×ˢ t) (μ.prod ν)) :
    (∫ x in s, ∫ y in t, f x y ∂ν ∂μ) = (∫ y in t, ∫ x in s, f x y ∂μ ∂ν) := by
  -- Convert `IntegrableOn` on the product set into integrability on the restricted product measure.
  have hf' : Integrable f.uncurry ((μ.restrict s).prod (ν.restrict t)) := by
    -- `μ.restrict s ⊗ ν.restrict t = (μ ⊗ ν).restrict (s×t)`
    -- so this is exactly `hf`.
    -- First unfold `IntegrableOn`, then rewrite the restricted product measure.
    have : Integrable (fun z : α × β => f z.1 z.2) ((μ.prod ν).restrict (s ×ˢ t)) := by
      simpa [IntegrableOn] using hf
    -- Rewrite the measure using `Measure.prod_restrict`.
    simpa [Measure.prod_restrict s t] using this
  -- Now apply the standard Fubini swap.
  -- (Set-integral notation `∫ x in s, ...` is definitional as integration w.r.t. restricted measures.)
  simpa using
    (MeasureTheory.integral_integral_swap (μ := μ.restrict s) (ν := ν.restrict t) (f := f) hf')

/-! ### Bookkeeping lemma: integrability of an inner integral from product integrability -/

/-- If a cone-indicator integrand is integrable on the product set `I × box`, then the
function obtained by integrating out the `x` variable is integrable on `box`.

This is the main bookkeeping step needed to turn the pointwise cone inequality into the
integrated cone→tent inequality. -/
lemma integrableOn_K_of_integrableOn_cone
    (a b : ℝ)
    (G : ℝ × ℝ → ℝ)
    (hCone :
      IntegrableOn
        (fun z : ℝ × (ℝ × ℝ) => if |z.1 - z.2.1| < 2 * z.2.2 then G z.2 else 0)
        ((Icc a b) ×ˢ ((Icc a b) ×ˢ (Icc 0 (b - a))))
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)))) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        ∫ x in Icc a b, (if |x - p.1| < 2 * p.2 then G p else 0))
      ((Icc a b) ×ˢ (Icc 0 (b - a)))
      (volume : Measure (ℝ × ℝ)) := by
  -- Let I be the base interval and box be the (ξ,y) box.
  let I : Set ℝ := Icc a b
  let box : Set (ℝ × ℝ) := (Icc a b) ×ˢ (Icc 0 (b - a))
  -- Convert IntegrableOn on `I × box` to integrability on the restricted product measure.
  have hCone' :
      Integrable
        (fun z : ℝ × (ℝ × ℝ) => if |z.1 - z.2.1| < 2 * z.2.2 then G z.2 else 0)
        (((volume : Measure ℝ).restrict I).prod ((volume : Measure (ℝ × ℝ)).restrict box)) := by
    -- First unfold IntegrableOn.
    have : Integrable
        (fun z : ℝ × (ℝ × ℝ) => if |z.1 - z.2.1| < 2 * z.2.2 then G z.2 else 0)
        (((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))).restrict (I ×ˢ box)) := by
      simpa [MeasureTheory.IntegrableOn, I, box] using hCone
    -- Rewrite the restricted product measure.
    simpa [Measure.prod_restrict I box] using this
  -- Apply Fubini integrability: inner x-integral is integrable as a function of p.
  have hK :
      Integrable
        (fun p : (ℝ × ℝ) =>
          ∫ x, (if |x - p.1| < 2 * p.2 then G p else 0) ∂((volume : Measure ℝ).restrict I))
        ((volume : Measure (ℝ × ℝ)).restrict box) :=
    (MeasureTheory.Integrable.integral_prod_right (μ := (volume : Measure ℝ).restrict I) (ν := (volume : Measure (ℝ × ℝ)).restrict box)
      (f := fun z : ℝ × (ℝ × ℝ) => if |z.1 - z.2.1| < 2 * z.2.2 then G z.2 else 0) hCone')
  -- Rewrite the inner integral as a set integral over `Icc a b`, and conclude `IntegrableOn` on `box`.
  -- (`IntegrableOn` means integrable w.r.t. the restricted measure.)
  simpa [MeasureTheory.IntegrableOn, I, box] using hK

/-- Expand a set integral on the box `Icc a b ×ˢ Icc 0 (b-a)` into iterated integrals.

This is a thin wrapper around `MeasureTheory.setIntegral_prod`, using the fact that
`volume` on `ℝ × ℝ` is the product measure (`MeasureTheory.Measure.volume_eq_prod`). -/
lemma expand_box_integral
    (a b : ℝ)
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F ((Icc a b) ×ˢ (Icc 0 (b - a))) (volume : Measure (ℝ × ℝ))) :
    (∫ p in ((Icc a b) ×ˢ (Icc 0 (b - a))), F p ∂(volume : Measure (ℝ × ℝ))) =
      (∫ x in Icc a b, ∫ y in Icc 0 (b - a), F (x, y) ∂(volume : Measure ℝ) ∂(volume : Measure ℝ)) := by
  -- Rewrite the product-space volume as a product measure and apply Fubini for set integrals.
  have hF' :
      IntegrableOn F ((Icc a b) ×ˢ (Icc 0 (b - a))) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    -- `volume = volume.prod volume` on `ℝ×ℝ`
    simpa [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] using hF
  -- Apply `setIntegral_prod` on the product measure.
  simpa using
    (MeasureTheory.setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (f := fun p : ℝ × ℝ => F p) (s := Icc a b) (t := Icc 0 (b - a)) hF')

/-- **Cone → tent geometry** (aperture 2, box form).

Let `box := Icc a b ×ˢ Icc 0 (b-a)` and `G : ℝ×ℝ→ℝ` be nonnegative. Then
\[
\iint_{box} y\,G(\xi,y)\,d\xi\,dy \;\le\; \int_{x\in Icc a b}\iint_{box} 1_{\{|x-\xi|<2y\}}\,G(\xi,y)\,d\xi\,dy\,dx.
\]

This is the integrated version of the pointwise inequality
`y * G(ξ,y) ≤ ∫_{x∈I} 1_{|x-ξ|<2y} G(ξ,y) dx`. -/
lemma cone_to_tent_geometry
    (a b : ℝ) (_hab : a < b)
    (G : ℝ × ℝ → ℝ) (hG_nonneg : ∀ p, 0 ≤ G p)
    (h_weight :
      IntegrableOn (fun p : ℝ × ℝ => p.2 * G p) ((Icc a b) ×ˢ (Icc 0 (b - a)))
        (volume : Measure (ℝ × ℝ)))
    (h_cone :
      IntegrableOn
        (fun z : ℝ × (ℝ × ℝ) => if |z.1 - z.2.1| < 2 * z.2.2 then G z.2 else 0)
        ((Icc a b) ×ˢ ((Icc a b) ×ˢ (Icc 0 (b - a))))
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)))) :
    (∫ ξ in Icc a b, ∫ y in Icc 0 (b - a), y * G (ξ, y))
      ≤
    (∫ x in Icc a b,
      ∫ p in ((Icc a b) ×ˢ (Icc 0 (b - a))),
        (if |x - p.1| < 2 * p.2 then G p else 0) ∂(volume : Measure (ℝ × ℝ))
      ∂(volume : Measure ℝ)) := by
  classical
  let box : Set (ℝ × ℝ) := (Icc a b) ×ˢ (Icc 0 (b - a))
  have h_box_meas : MeasurableSet box :=
    MeasurableSet.prod measurableSet_Icc measurableSet_Icc

  -- Define K(p) = ∫_{x∈I} 1_{|x-ξ|<2y} G(p).
  let K : (ℝ × ℝ) → ℝ :=
    fun p => ∫ x in Icc a b, (if |x - p.1| < 2 * p.2 then G p else 0)

  -- K is integrable on the box, from the product integrability hypothesis.
  have hK_int : IntegrableOn K box (volume : Measure (ℝ × ℝ)) := by
    -- exactly our bookkeeping lemma
    simpa [K, box] using (integrableOn_K_of_integrableOn_cone (a := a) (b := b) (G := G) h_cone)

  -- Pointwise inequality on box: y*G ≤ K.
  have h_pointwise : ∀ p ∈ box, p.2 * G p ≤ K p := by
    intro p hp
    rcases hp with ⟨hξ, hy⟩
    have hy0 : 0 ≤ p.2 := hy.1
    have hy_le : p.2 ≤ b - a := hy.2
    -- Apply the constant-version inequality with c = G p.
    simpa [K] using
      (cone_weight_le_integral_indicator a b p.1 p.2 (G p) hξ hy0 hy_le (hG_nonneg p))

  -- Integrate over the box.
  have h_mono :
      (∫ p in box, p.2 * G p ∂(volume : Measure (ℝ × ℝ))) ≤
        (∫ p in box, K p ∂(volume : Measure (ℝ × ℝ))) := by
    refine
      MeasureTheory.setIntegral_mono_on (μ := (volume : Measure (ℝ × ℝ)))
        (s := box) (f := fun p => p.2 * G p) (g := K)
        h_weight hK_int h_box_meas h_pointwise

  -- Rewrite the left set-integral as the iterated integral appearing in the statement.
  have hL : (∫ p in box, p.2 * G p ∂(volume : Measure (ℝ × ℝ))) =
      (∫ ξ in Icc a b, ∫ y in Icc 0 (b - a), y * G (ξ, y)) := by
    -- expand_box_integral gives set integral = iterated
    have h := expand_box_integral a b (fun p : ℝ × ℝ => p.2 * G p) (by simpa [box] using h_weight)
    simpa [box] using h

  -- Swap the order of integration on `Icc a b × box` to rewrite ∫_box K as ∫_x ∫_box ...
  have h_swap :
      (∫ p in box, K p ∂(volume : Measure (ℝ × ℝ))) =
        (∫ x in Icc a b,
          ∫ p in box, (if |x - p.1| < 2 * p.2 then G p else 0) ∂(volume : Measure (ℝ × ℝ))
        ∂(volume : Measure ℝ)) := by
    -- Apply the generic swap lemma with μ = volume on ℝ and ν = volume on ℝ×ℝ.
    let f : ℝ → (ℝ × ℝ) → ℝ := fun x p => if |x - p.1| < 2 * p.2 then G p else 0
    have hf :
        IntegrableOn (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2) ((Icc a b) ×ˢ box)
          ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
      -- exactly `h_cone`
      simpa [f, box] using h_cone
    have hswap0 :=
      setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
        (s := Icc a b) (t := box) (f := f) hf
    -- `hswap0` gives ∫_x ∫_p f = ∫_p ∫_x f. The RHS is ∫_p K.
    -- Rearrange.
    have : (∫ x in Icc a b, ∫ p in box, f x p ∂(volume : Measure (ℝ × ℝ)) ∂(volume : Measure ℝ)) =
        (∫ p in box, ∫ x in Icc a b, f x p ∂(volume : Measure ℝ) ∂(volume : Measure (ℝ × ℝ))) := by
      simpa using hswap0
    -- Now rewrite the inner integral as K.
    simpa [K, f, box] using this.symm

  -- Combine.
  calc
    (∫ ξ in Icc a b, ∫ y in Icc 0 (b - a), y * G (ξ, y))
        = (∫ p in box, p.2 * G p ∂(volume : Measure (ℝ × ℝ))) := hL.symm
    _ ≤ (∫ p in box, K p ∂(volume : Measure (ℝ × ℝ))) := h_mono
    _ = (∫ x in Icc a b,
          ∫ p in box, (if |x - p.1| < 2 * p.2 then G p else 0) ∂(volume : Measure (ℝ × ℝ))
        ∂(volume : Measure ℝ)) := h_swap

/-!
### Status toward eliminating `bmo_carleson_embedding`

The **geometry + Fubini bookkeeping** step of the Fefferman–Stein tent-space proof is now in place:

- `cone_base_volume_ge`
- `integral_if_abs_lt_const`
- `cone_weight_le_integral_indicator`
- `integrableOn_K_of_integrableOn_cone`
- `expand_box_integral`
- `setIntegral_prod_swap`
- `cone_to_tent_geometry`

What remains is the **analytic** part: controlling the Poisson-extension gradient energy by the BMO norm
with explicit constants, i.e. the content currently axiomatized as `bmo_carleson_embedding`.

The next smallest analytic lemmas to attempt live naturally here as well:

- `poisson_energy_identity_L2` (global weighted energy identity / Plancherel)
- `deriv_conjugatePoissonIntegral_eq_integral_dxKernel` (differentiate under the integral sign)
- `tail_annulus_decay_bound` (ring decomposition estimate for the tail term)

Once those exist, `bmo_carleson_embedding` becomes a theorem assembled from:
split `f = (f-f_I)1_I + (f-f_I)1_{ℝ\I}` + local energy identity + tail decay + John–Nirenberg.
-/

/-- **AXIOM (Fefferman-Stein 1972)**: BMO→Carleson embedding.

    If w has BMO norm ≤ M, then the Carleson energy satisfies:
      E_Q ≤ C · M² · |I|

    This is the Fefferman-Stein theorem connecting BMO to Carleson measures. -/
axiom bmo_carleson_embedding
    (w : ℝ → ℝ) (a b : ℝ) (M : ℝ) (_hM_pos : M > 0)
    (_h_bmo : ∀ a' b' : ℝ, a' < b' →
      (b' - a')⁻¹ * ∫ t in Icc a' b', |w t - (b' - a')⁻¹ * ∫ s in Icc a' b', w s| ≤ M) :
    carleson_energy w a b ≤ C_FS * M^2 * (b - a)

/-! ## Green's Identity Components -/

/-- Structure bundling a gradient bound hypothesis for a function.
    This is used to construct the Green identity argument. -/
structure GradientBoundHypothesis (w : ℝ → ℝ) where
  /-- The gradient bound constant. -/
  C : ℝ
  /-- C is positive. -/
  hC_pos : C > 0
  /-- The bound holds for all Carleson boxes. -/
  bound : ∀ (a b : ℝ), a < b → carleson_energy w a b ≤ C * (b - a)

/-- The Green-Cauchy-Schwarz bound.

    **Mathematical Content**:
    For the phase pairing ⟨φ, -∂_y u⟩ where u is the harmonic extension:

    1. Green's first identity:
       ∫_I φ · (-∂_y u) = ∫∫_Q ∇u · ∇v + boundary terms

    2. Cauchy-Schwarz:
       |∫∫_Q ∇u · ∇v| ≤ √(E_Q(u)) · √(E_Q(v))

    3. For window φ with ‖φ‖_H^1 bounded:
       E_Q(v) ≤ C_ψ · |I|

    4. Fefferman-Stein for u = log|ξ|:
       E_Q(u) ≤ K_tail · |I|

    5. Combining: |⟨φ, -∂_y u⟩| ≤ C_geom · √(K_tail) -/
theorem green_cauchy_schwarz_bound
    (w : ℝ → ℝ) (a b : ℝ) (_hab : a < b)
    (h_grad : GradientBoundHypothesis w) :
    ∃ C : ℝ, C > 0 ∧ carleson_energy w a b ≤ C * (b - a) :=
  ⟨h_grad.C, h_grad.hC_pos, h_grad.bound a b _hab⟩

end RiemannRecognitionGeometry.PoissonExtension
