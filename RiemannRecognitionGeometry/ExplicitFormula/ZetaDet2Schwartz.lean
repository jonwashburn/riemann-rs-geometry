/-
# Route 3: det₂ analytic obligations for the Schwartz/Fourier `TestSpace`

This file fills `ZetaInstantiation.ZetaDet2AnalyticAssumptions` for the concrete
`SchwartzTestSpace` (`F := SchwartzMap ℝ ℂ`), assuming only `1 < LC.c` and taking the Fourier
inversion identity as an explicit hypothesis parameter.
-/

import RiemannRecognitionGeometry.ExplicitFormula.ZetaInstantiation
import RiemannRecognitionGeometry.ExplicitFormula.SchwartzTestSpace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace ZetaInstantiation

open Complex MeasureTheory Real SchwartzMap
open scoped BigOperators

namespace Schwartz

/-! ## Summability of the von Mangoldt weight on `Re(s)=c>1` -/

theorem summable_norm_vonMangoldt_mul_rpow_neg {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-c)) := by
  classical
  -- Choose `δ := (c-1)/2`, so `c-δ = (c+1)/2 > 1`.
  set δ : ℝ := (c - 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hcδ : (1 : ℝ) < c - δ := by dsimp [δ]; linarith

  -- Summability of the comparison p-series `∑ (n^(c-δ))⁻¹`.
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ (c - δ))⁻¹) := by
    simpa using (Real.summable_nat_rpow_inv (p := c - δ)).2 hcδ
  have hsum' : Summable (fun n : ℕ => (1 / δ) * ((n : ℝ) ^ (c - δ))⁻¹) := by
    simpa using hsum.mul_left (1 / δ)

  -- Set `g` = target series term, `f` = comparison series term.
  let g : ℕ → ℝ := fun n => ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-c)
  let f : ℕ → ℝ := fun n => (1 / δ) * ((n : ℝ) ^ (c - δ))⁻¹

  have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := by
    intro n
    dsimp [g]
    have h1 : 0 ≤ ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := by
      -- go through `abs` to avoid definitional-equality issues for `‖·‖` on `ℂ`
      simpa [Complex.norm_eq_abs] using (Complex.abs.nonneg (↑(ArithmeticFunction.vonMangoldt n) : ℂ))
    have h2 : 0 ≤ (n : ℝ) ^ (-c) := Real.rpow_nonneg (Nat.cast_nonneg n) (-c)
    exact mul_nonneg h1 h2

  have hgf : ∀ n : ℕ, g n ≤ f n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hc_ne : (-c : ℝ) ≠ 0 := by linarith
      have hcd_ne : (c - δ : ℝ) ≠ 0 := by linarith
      simp [g, f, ArithmeticFunction.map_zero, Real.zero_rpow hc_ne, Real.zero_rpow hcd_ne]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n

    have hΛnorm : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = (ArithmeticFunction.vonMangoldt n) := by
      have hnonnegΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n) :=
        ArithmeticFunction.vonMangoldt_nonneg (n := n)
      simp [Complex.norm_eq_abs, _root_.abs_of_nonneg hnonnegΛ]

    have hΛle : (ArithmeticFunction.vonMangoldt n) ≤ Real.log (n : ℝ) := by
      simpa using (ArithmeticFunction.vonMangoldt_le_log (n := n))
    have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ :=
      Real.log_le_rpow_div hn0 hδ
    have hΛbd : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ (1 / δ) * (n : ℝ) ^ δ := by
      rw [hΛnorm]
      have : (ArithmeticFunction.vonMangoldt n) ≤ (n : ℝ) ^ δ / δ := le_trans hΛle hlog_le
      simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using this

    have hpow : (n : ℝ) ^ δ * (n : ℝ) ^ (-c) = (n : ℝ) ^ (-(c - δ)) := by
      have := (Real.rpow_add hnpos' δ (-c)).symm
      have hExp : δ + (-c) = -(c - δ) := by ring
      simpa [hExp] using this

    have hrpow_inv : (n : ℝ) ^ (-(c - δ)) = ((n : ℝ) ^ (c - δ))⁻¹ := by
      simpa using (Real.rpow_neg hn0 (c - δ))

    have hmul := mul_le_mul_of_nonneg_right hΛbd (Real.rpow_nonneg (Nat.cast_nonneg n) (-c))

    dsimp [g, f]
    calc
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-c)
          ≤ ((1 / δ) * (n : ℝ) ^ δ) * (n : ℝ) ^ (-c) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = (1 / δ) * ((n : ℝ) ^ δ * (n : ℝ) ^ (-c)) := by
            ring
      _ = (1 / δ) * (n : ℝ) ^ (-(c - δ)) := by
            -- rewrite the `rpow` product without cancellation
            simp [hpow]
      _ = (1 / δ) * ((n : ℝ) ^ (c - δ))⁻¹ := by
            -- avoid `simp` (it triggers `mul_eq_mul_left_iff`)
            rw [hrpow_inv]

  simpa [g, f] using (Summable.of_nonneg_of_le hg_nonneg hgf hsum')

/-! ## Filling `ZetaDet2AnalyticAssumptions` for `SchwartzTestSpace` -/

def zetaDet2AnalyticAssumptions_schwartz
    (LC : LagariasContourFramework (SchwartzMap ℝ ℂ))
    (hc : 1 < LC.c)
    (hFI :
      ExplicitFormulaCancellationSkeleton.FourierInversionDirichletTerm
        (F := SchwartzMap ℝ ℂ)
        (c := LC.c) (hc := (by linarith : 1/2 < LC.c))
        (testValue := mellinOnCriticalLine (F := SchwartzMap ℝ ℂ))) :
    ZetaDet2AnalyticAssumptions (F := SchwartzMap ℝ ℂ) (LC := LC) where
  hc := by linarith
  fourier_inversion := hFI
  integrable_term := by
    intro h n hn
    -- `M[h](c+it)` is Schwartz (Fourier transform), hence integrable.
    have hM : Integrable (fun t : ℝ => M[h]((LC.c : ℂ) + (t : ℂ) * I)) (volume : Measure ℝ) := by
      have : Integrable (fun t : ℝ => (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) h) t) (volume : Measure ℝ) :=
        (SchwartzMap.integrable (f := (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) h)) (μ := (volume : Measure ℝ)))
      simpa [TestSpace.Mellin, SchwartzTestSpace.Mellin] using this
    -- bounded factor in `t`
    let f : ℝ → ℂ :=
      fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((LC.c : ℂ) + (t : ℂ) * I))
    have hf_meas : AEStronglyMeasurable f (volume : Measure ℝ) := by
      -- continuity (for `n ≥ 1`) gives `AEStronglyMeasurable`
      have hn0 : (n : ℂ) ≠ 0 := by
        have : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
        exact_mod_cast this
      letI : NeZero (n : ℂ) := ⟨hn0⟩
      have hpow : Continuous (fun z : ℂ => (n : ℂ) ^ z) := by
        simpa using (continuous_const_cpow (z := (n : ℂ)))
      have hexp : Continuous (fun t : ℝ => (-((LC.c : ℂ) + (t : ℂ) * I) : ℂ)) := by
        continuity
      have hcont : Continuous fun t : ℝ => (n : ℂ) ^ (-((LC.c : ℂ) + (t : ℂ) * I)) :=
        hpow.comp hexp
      have hcont' : Continuous f := by
        -- multiply by the constant `Λ(n)`
        simpa [f, mul_assoc] using (continuous_const.mul hcont)
      exact hcont'.aestronglyMeasurable
    have hf_bound :
        ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
          ‖f t‖ ≤ ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c) := by
      refine Filter.Eventually.of_forall ?_
      intro t
      by_cases hn0 : n = 0
      · subst hn0
        -- then `Λ(0)=0`, so `f t = 0`
        simp [f, ArithmeticFunction.map_zero]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hcpow :
          ‖(n : ℂ) ^ (-((LC.c : ℂ) + (t : ℂ) * I))‖ = (n : ℝ) ^ (-LC.c) := by
        have habs :=
          (Complex.abs_cpow_eq_rpow_re_of_pos (x := (n : ℝ)) (hx := (Nat.cast_pos.mpr hnpos))
            (y := (-((LC.c : ℂ) + (t : ℂ) * I))))
        simpa [Complex.norm_eq_abs] using habs
      -- compute the norm exactly (avoid `simp` cancelling common factors into disjunctions)
      have hf_eq :
          ‖f t‖ = ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c) := by
        dsimp [f]
        calc
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
                (n : ℂ) ^ (-((LC.c : ℂ) + (t : ℂ) * I))‖
              =
              ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ *
                ‖(n : ℂ) ^ (-((LC.c : ℂ) + (t : ℂ) * I))‖ := by
                  simpa using
                    (norm_mul (ArithmeticFunction.vonMangoldt n : ℂ)
                      ((n : ℂ) ^ (-((LC.c : ℂ) + (t : ℂ) * I))))
          _ = ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c) := by
                rw [hcpow]
      exact le_of_eq hf_eq
    -- apply `bdd_mul'` with the bounded factor `f`
    have hprod : Integrable (fun t : ℝ => f t * M[h]((LC.c : ℂ) + (t : ℂ) * I)) (volume : Measure ℝ) :=
      hM.bdd_mul' hf_meas hf_bound
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using hprod
  summable_integral_norm := by
    intro h
    -- Integrability of the norm of `M[h](c+it)`.
    have hM : Integrable (fun t : ℝ => M[h]((LC.c : ℂ) + (t : ℂ) * I)) (volume : Measure ℝ) := by
      have : Integrable (fun t : ℝ => (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) h) t) (volume : Measure ℝ) :=
        (SchwartzMap.integrable (f := (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) h)) (μ := (volume : Measure ℝ)))
      simpa [TestSpace.Mellin, SchwartzTestSpace.Mellin] using this
    let C : ℝ := ∫ t : ℝ, ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ ∂ (volume : Measure ℝ)

    -- Summable weights in `n`.
    have hSumΛ : Summable (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)) :=
      summable_norm_vonMangoldt_mul_rpow_neg (c := LC.c) hc

    -- Compare termwise to `C * (‖Λ(n)‖ * n^{-c})`.
    let g : ℕ → ℝ := fun n : ℕ =>
      ∫ t : ℝ, ‖M[h]((LC.c : ℂ) + (t : ℂ) * I) *
        (ArithmeticFunction.vonMangoldt n : ℂ) *
        (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))‖ ∂ (volume : Measure ℝ)
    let f : ℕ → ℝ := fun n : ℕ =>
      C * (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c))

    have hf_summable : Summable f := by
      simpa [f] using (hSumΛ.mul_left C)

    have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := by
      intro n
      dsimp [g]
      refine MeasureTheory.integral_nonneg ?_
      intro t
      exact norm_nonneg
        (M[h]((LC.c : ℂ) + (t : ℂ) * I) *
          (ArithmeticFunction.vonMangoldt n : ℂ) *
          (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I))))

    have hgf : ∀ n : ℕ, g n ≤ f n := by
      intro n
      by_cases hn : n = 0
      · subst hn
        have hc_ne : (-LC.c : ℝ) ≠ 0 := by linarith
        -- Λ(0)=0 and 0^(-c)=0
        simp [g, f, C, ArithmeticFunction.map_zero, Real.zero_rpow hc_ne]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn

      have hpoint :
          ∀ t : ℝ,
            ‖M[h]((LC.c : ℂ) + (t : ℂ) * I) *
                (ArithmeticFunction.vonMangoldt n : ℂ) *
                (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))‖
              ≤
              ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ *
                (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)) := by
        intro t
        have hcpow :
            ‖(n : ℂ) ^ (-((LC.c : ℂ) + (t : ℂ) * I))‖ = (n : ℝ) ^ (-LC.c) := by
          have habs :
              Complex.abs ((n : ℂ) ^ (-((LC.c : ℂ) + (t : ℂ) * I))) = (n : ℝ) ^ (-LC.c) := by
            simpa using
              (Complex.abs_cpow_eq_rpow_re_of_pos (x := (n : ℝ)) (hx := (Nat.cast_pos.mpr hnpos))
                (y := (-((LC.c : ℂ) + (t : ℂ) * I))))
          simpa [Complex.norm_eq_abs] using habs
        -- basic norm algebra (compute an equality, then turn it into `≤`)
        have hEq :
            ‖M[h]((LC.c : ℂ) + (t : ℂ) * I) *
                  (ArithmeticFunction.vonMangoldt n : ℂ) *
                  (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))‖
              =
              ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ *
                (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)) := by
          calc
            ‖M[h]((LC.c : ℂ) + (t : ℂ) * I) *
                  (ArithmeticFunction.vonMangoldt n : ℂ) *
                  (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))‖
                = ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ *
                    (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ *
                      ‖(n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))‖) := by
                      simp [norm_mul, mul_assoc, mul_left_comm, mul_comm]
            _ = ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ *
                  (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)) := by
                    rw [hcpow]
        exact le_of_eq hEq

      have hmono :
          g n ≤
            (∫ t : ℝ,
                ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ *
                  (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)) ∂ (volume : Measure ℝ)) := by
        dsimp [g]
        -- use `integral_mono_of_nonneg` with an integrable majorant
        have hgi :
            Integrable
              (fun t : ℝ =>
                ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ *
                  (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)))
              (volume : Measure ℝ) := by
          -- `‖M[h](c+it)‖` is integrable, and the remaining factor is constant in `t`.
          have hMn : Integrable (fun t : ℝ => ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖) (volume : Measure ℝ) :=
            hM.norm
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (hMn.mul_const (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)))
        have h0 :
            (fun _t : ℝ => (0 : ℝ)) ≤ᵐ[volume]
              fun t : ℝ =>
                ‖M[h]((LC.c : ℂ) + (t : ℂ) * I) *
                    (ArithmeticFunction.vonMangoldt n : ℂ) *
                    (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))‖ := by
          exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
        have hle :
            (fun t : ℝ =>
                ‖M[h]((LC.c : ℂ) + (t : ℂ) * I) *
                    (ArithmeticFunction.vonMangoldt n : ℂ) *
                    (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))‖)
              ≤ᵐ[volume]
              fun t : ℝ =>
                ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ *
                  (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)) := by
          exact Filter.Eventually.of_forall (fun t => hpoint t)
        exact MeasureTheory.integral_mono_of_nonneg h0 hgi hle

      have hconst :
          (∫ t : ℝ,
              ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖ *
                (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)) ∂ (volume : Measure ℝ))
            =
            f n := by
        -- pull out the constant factor using `integral_mul_right`
        dsimp [f, C]
        -- `∫ (‖M‖ * r) = (∫ ‖M‖) * r`
        simpa [mul_assoc] using
          (MeasureTheory.integral_mul_right (μ := (volume : Measure ℝ))
            (r := (‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-LC.c)))
            (fun t : ℝ => ‖M[h]((LC.c : ℂ) + (t : ℂ) * I)‖))

      exact le_trans hmono (le_of_eq hconst)

    exact Summable.of_nonneg_of_le hg_nonneg hgf hf_summable

end Schwartz

end ZetaInstantiation
end ExplicitFormula
end RiemannRecognitionGeometry
