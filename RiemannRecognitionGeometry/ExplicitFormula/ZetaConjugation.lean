/-
# Zeta Conjugation Symmetry

Ported from `riemann-joint-new/riemann/PrimeNumberTheoremAnd/ZetaConj.lean`.

Proves that `riemannZeta (conj s) = conj (riemannZeta s)` and similar identities.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.MellinTransform

open scoped Complex ComplexConjugate

noncomputable section

open Complex Set MeasureTheory

/-!
## HasDerivAt for conjugated functions

Ported from riemann-joint-new.
-/

/-- The composition conj ∘ f ∘ conj is differentiable where f is differentiable.
If f has derivative a at p, then conj ∘ f ∘ conj has derivative conj(a) at conj(p). -/
theorem hasDerivAt_conj_conj {f : ℂ → ℂ} {p a : ℂ} (hf : HasDerivAt f a p) :
    HasDerivAt (fun z ↦ conj (f (conj z))) (conj a) (conj p) := by
  rw [hasDerivAt_iff_tendsto] at hf ⊢
  have hcont := Complex.continuous_conj.tendsto (conj p)
  rw [Complex.conj_conj] at hcont
  have hcomp := Filter.Tendsto.comp hf hcont
  convert hcomp with z
  simp only [Complex.conj_conj, smul_eq_mul, Function.comp_apply]
  -- Goal: ‖z - conj p‖⁻¹ * ‖conj(f(conj z)) - conj(f p) - (z - conj p) * conj a‖
  --     = ‖conj z - p‖⁻¹ * ‖f(conj z) - f p - (conj z - p) * a‖
  -- First show the denominators are equal
  have hden : ‖z - conj p‖ = ‖conj z - p‖ := by
    have : z - conj p = conj (conj z - p) := by simp
    rw [this, Complex.norm_eq_abs, Complex.abs_conj, ← Complex.norm_eq_abs]
  -- Now show the numerators are equal
  have hnum : ‖conj (f (conj z)) - conj (f p) - (z - conj p) * conj a‖ =
              ‖f (conj z) - f p - (conj z - p) * a‖ := by
    have h1 : conj (f (conj z)) - conj (f p) - (z - conj p) * conj a =
              conj (f (conj z) - f p - (conj z - p) * a) := by
      simp [map_sub, map_mul, Complex.conj_conj]
    rw [h1, Complex.norm_eq_abs, Complex.abs_conj, ← Complex.norm_eq_abs]
  rw [hden, hnum]

/-- The derivative of conj ∘ f ∘ conj at conj(p) equals conj(f'(p)). -/
theorem deriv_conj_conj (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  set g := fun z ↦ conj (f (conj z))
  by_cases hf : DifferentiableAt ℂ f p
  · exact (hasDerivAt_conj_conj hf.hasDerivAt).deriv
  · by_cases hg : DifferentiableAt ℂ g (conj p)
    · -- If the conjugated function were differentiable, then f would be differentiable
      have : DifferentiableAt ℂ f p := by
        convert (hasDerivAt_conj_conj hg.hasDerivAt).differentiableAt using 2 <;> simp [g]
      contradiction
    · -- Both derivatives are zero when the functions are not differentiable
      rw [deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt hf, map_zero]

/-!
## Conjugation symmetry of riemannZeta
-/

/-- Conjugation symmetry of riemannZeta in the half-plane Re(s) > 1. -/
lemma conj_riemannZeta_conj_aux1 (s : ℂ) (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow]
  swap
  · simpa
  rw [Complex.conj_tsum]
  congr
  ext n
  have hn : n + 1 ≠ 0 := by linarith
  have hn' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn']
  rw [Complex.cpow_def_of_ne_zero hn']
  rw [RCLike.conj_div, map_one, ← Complex.exp_conj, map_mul, Complex.conj_conj]
  norm_cast
  rw [Complex.conj_ofReal]

/-- Conjugation symmetry of riemannZeta: conj(ζ(conj s)) = ζ(s).

Ported from riemann-joint-new/riemann/PrimeNumberTheoremAnd/ZetaConj.lean.
Uses analytic continuation from Re(s) > 1.
-/
theorem conj_riemannZeta_conj (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one, Complex.conj_eq_iff_real]
    rw [riemannZeta_one]
    use (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
    norm_cast
    rw [← Complex.ofReal_log]
    · push_cast
      rfl
    · positivity
  · let U : Set ℂ := {1}ᶜ
    let g := fun s ↦ conj (riemannZeta (conj s))
    suffices Set.EqOn g riemannZeta U by
      apply this
      rwa [Set.mem_compl_singleton_iff]
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2)
    · simp [U]
    · rw [Filter.eventuallyEq_iff_exists_mem]
      set V := Complex.re ⁻¹' (Ioi 1)
      use V
      constructor
      · have Vopen : IsOpen V := Continuous.isOpen_preimage Complex.continuous_re _ isOpen_Ioi
        have two_in_V : 2 ∈ V := by simp [V]
        exact IsOpen.mem_nhds Vopen two_in_V
      · intro s hs
        exact conj_riemannZeta_conj_aux1 s hs
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      have hs₁' : conj s₁ ≠ 1 := (map_ne_one_iff (starRingEnd ℂ) (RingHom.injective (starRingEnd ℂ))).mpr hs₁
      -- Need: conj ∘ riemannZeta ∘ conj is differentiable at s₁
      have hdiff : DifferentiableAt ℂ riemannZeta (conj s₁) := differentiableAt_riemannZeta hs₁'
      -- The composition conj ∘ f ∘ conj is differentiable when f is
      have hcomp : DifferentiableAt ℂ (fun z => conj (riemannZeta (conj z))) s₁ := by
        -- Use hasDerivAt_conj_conj: if f has derivative at p, then conj ∘ f ∘ conj has derivative at conj(p)
        -- Here: riemannZeta is differentiable at conj(s₁), so conj ∘ ζ ∘ conj is differentiable at conj(conj(s₁)) = s₁
        have hder := hasDerivAt_conj_conj hdiff.hasDerivAt
        simp only [Complex.conj_conj] at hder
        exact hder.differentiableAt
      exact hcomp.differentiableWithinAt
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      exact (differentiableAt_riemannZeta hs₁).differentiableWithinAt
    · refine (?_ : IsConnected U).isPreconnected
      refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
      simp

/-- Conjugation symmetry of riemannZeta: ζ(conj s) = conj(ζ(s)). -/
theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rw [← conj_riemannZeta_conj, Complex.conj_conj]

/-- Conjugation symmetry of the derivative of riemannZeta.

The derivative of ζ satisfies: ζ'(conj s) = conj(ζ'(s)).
This follows from differentiating ζ(conj s) = conj(ζ(s)). -/
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  -- conj_riemannZeta_conj says: conj(ζ(conj z)) = ζ(z) for all z
  -- Hence ζ(z) = conj(ζ(conj z)), so ζ = conj ∘ ζ ∘ conj
  -- By deriv_conj_conj: deriv(conj ∘ f ∘ conj) at conj(p) = conj(deriv f p)
  simp only [← deriv_conj_conj, conj_riemannZeta_conj]

/-- Conjugation symmetry of the log-derivative of riemannZeta. -/
theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

/-- Conjugation symmetry of logDeriv riemannZeta. -/
theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

/-!
## Conjugation symmetry of completedRiemannZeta

This requires proving conjugation symmetry for Gammaℝ and the completed zeta.
-/

/-!
### A small Mellin–conjugation helper

`completedRiemannZeta₀` is defined in Mathlib via Hurwitz’s completed zeta as a Mellin transform
(`WeakFEPair.Λ₀ = mellin f_modif`).  For the conjugation symmetry of `completedRiemannZeta₀` we use:

> If `f : ℝ → ℂ` is pointwise fixed by conjugation, then `mellin f` commutes with conjugation.

We keep this lemma `private` since it is just local glue for the `completedRiemannZeta₀_conj` proof.
-/

private lemma mellin_star_of_star_fixed (f : ℝ → ℂ)
    (hf : ∀ t, starRingEnd ℂ (f t) = f t) (s : ℂ) :
    mellin f (starRingEnd ℂ s) = starRingEnd ℂ (mellin f s) := by
  -- Unfold Mellin as an integral over `t > 0`.
  simp [mellin]
  have hs_meas : MeasurableSet (Set.Ioi (0 : ℝ)) := isOpen_Ioi.measurableSet

  -- Establish AE equality of integrands on the restricted measure `volume.restrict (Ioi 0)`.
  have hAE :
      (fun t : ℝ => ((t : ℂ) ^ (starRingEnd ℂ s - 1)) • f t) =ᵐ[volume.restrict (Set.Ioi 0)]
        fun t : ℝ => starRingEnd ℂ (((t : ℂ) ^ (s - 1)) • f t) := by
    -- Reduce `∀ᵐ` on the restricted measure to `∀ᵐ` on `volume` plus a membership hypothesis.
    refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ)) hs_meas).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht0 : 0 < t := by simpa using ht

    -- For `t>0`, `(t : ℂ)` is a positive real so `arg(t)=0≠π`, enabling `Complex.cpow_conj`.
    have harg : (t : ℂ).arg = 0 := by
      simpa using (Complex.arg_ofReal_of_nonneg (show 0 ≤ t from le_of_lt ht0))
    have hne : (t : ℂ).arg ≠ Real.pi := by
      have : (0 : ℝ) ≠ Real.pi := by exact ne_of_lt Real.pi_pos
      simpa [harg] using this
    have htstar : starRingEnd ℂ (t : ℂ) = (t : ℂ) := by simp

    have hsstar : starRingEnd ℂ (s - 1) = starRingEnd ℂ s - 1 := by
      simp [map_sub]

    have hpow : starRingEnd ℂ ((t : ℂ) ^ (s - 1)) = (t : ℂ) ^ (starRingEnd ℂ (s - 1)) := by
      have h := (Complex.cpow_conj (x := (t : ℂ)) (n := (s - 1)) hne)
      -- `cpow_conj` gives `t^(conj(s-1)) = conj((conj t)^(s-1))`; for real `t`, `conj t = t`.
      simpa [htstar] using h.symm

    -- Push conjugation through the integrand.
    simp [smul_eq_mul, hf t, hsstar, hpow]

  have hInt :
      (∫ t : ℝ in Set.Ioi 0, ((t : ℂ) ^ (starRingEnd ℂ s - 1)) • f t) =
        ∫ t : ℝ in Set.Ioi 0, starRingEnd ℂ (((t : ℂ) ^ (s - 1)) • f t) := by
    simpa using (MeasureTheory.integral_congr_ae (μ := volume.restrict (Set.Ioi 0)) hAE)

  -- Conclude by `integral_conj` over the restricted measure.
  calc
    (∫ t : ℝ in Set.Ioi 0, ((t : ℂ) ^ (starRingEnd ℂ s - 1)) • f t) =
        ∫ t : ℝ in Set.Ioi 0, starRingEnd ℂ (((t : ℂ) ^ (s - 1)) • f t) := hInt
    _ = starRingEnd ℂ (∫ t : ℝ in Set.Ioi 0, ((t : ℂ) ^ (s - 1)) • f t) := by
        simpa [Measure.restrict_restrict] using
          (integral_conj (μ := (volume.restrict (Set.Ioi 0)))
            (f := fun t : ℝ => ((t : ℂ) ^ (s - 1)) • f t))

/-- Conjugation symmetry of complex power with positive real base. -/
theorem cpow_conj_of_pos {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ conj s = conj ((x : ℂ) ^ s) := by
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.exp_conj, map_mul]
  congr 1
  -- log(x) is real for positive real x, so conj(log(x)) = log(x)
  have hlog_real : (Complex.log (x : ℂ)).im = 0 := by
    rw [Complex.log_im]
    have : Complex.arg (x : ℂ) = 0 := Complex.arg_ofReal_of_nonneg hx.le
    simp only [this]
  rw [Complex.conj_eq_iff_im.mpr hlog_real]

/-- Conjugation symmetry of Gammaℝ. -/
theorem Gammaℝ_conj (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  simp only [Complex.Gammaℝ]
  rw [map_mul]
  congr 1
  · -- π^(-conj(s)/2) = conj(π^(-s/2))
    have h1 : -(conj s) / 2 = conj (-s / 2) := by
      simp only [neg_div, map_neg, map_div₀, Complex.conj_ofReal]
      have : (starRingEnd ℂ) (2 : ℂ) = 2 := by norm_num [starRingEnd_apply]
      rw [this]
    rw [h1, cpow_conj_of_pos Real.pi_pos]
  · -- Γ(conj(s)/2) = conj(Γ(s/2))
    have h2 : conj s / 2 = conj (s / 2) := by
      simp only [map_div₀, Complex.conj_ofReal]
      have : (starRingEnd ℂ) (2 : ℂ) = 2 := by norm_num [starRingEnd_apply]
      rw [this]
    rw [h2, Complex.Gamma_conj]

/-!
### Conjugation symmetry of `completedRiemannZeta₀`

Mathlib defines:

`completedRiemannZeta₀ s = HurwitzZeta.completedHurwitzZetaEven₀ 0 s`
with
`HurwitzZeta.completedHurwitzZetaEven₀ a s = (HurwitzZeta.hurwitzEvenFEPair a).Λ₀ (s/2) / 2`
and `Λ₀ = mellin f_modif`.

For `a = 0` the kernel `f_modif` is real-valued (as a function into `ℂ`), hence fixed by conjugation,
so the Mellin–conjugation lemma above applies.
-/

private lemma hurwitzEvenFEPair0_f_modif_star_fixed (t : ℝ) :
    starRingEnd ℂ (((HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t)) =
      ((HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t) := by
  by_cases h1 : 1 < t
  · by_cases h2 : 0 < t ∧ t < 1
    · simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, h1, h2]
    · simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, h1, h2]
  · by_cases h2 : 0 < t ∧ t < 1
    · simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, h1, h2]
    · simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, h1, h2]

private theorem completedRiemannZeta₀_star (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
  -- Unfold `completedRiemannZeta₀` through Hurwitz’s completion; reduce to a Mellin identity.
  simp [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀, WeakFEPair.Λ₀]

  -- Rewrite the harmless scalar `starRingEnd ℂ 2 = 2` without `simp` loops.
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simp [starRingEnd_apply]

  -- Numerator identity: Mellin commutes with conjugation when the kernel is fixed by conjugation.
  have hnum :
      mellin (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif ((starRingEnd ℂ) s / 2) =
        (starRingEnd ℂ)
          (mellin (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif (s / 2)) := by
    have hM :=
      mellin_star_of_star_fixed
        (f := (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif)
        (fun t => hurwitzEvenFEPair0_f_modif_star_fixed t)
        (s / 2)
    -- `starRingEnd (s/2) = starRingEnd s / starRingEnd 2 = starRingEnd s / 2`.
    simpa [map_div₀, h2] using hM

  -- Divide both sides of the numerator identity by 2, matching the definition.
  have := congrArg (fun z : ℂ => z / 2) hnum
  simpa [h2] using this

/-- Conjugation symmetry of `completedRiemannZeta₀`. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  -- Convert the `starRingEnd` statement to the `conj` statement by rewriting.
  have hs : conj s = starRingEnd ℂ s := by
    -- Rewriting the RHS by `starRingEnd_apply` closes the goal.
    rw [starRingEnd_apply]
  have hs2 : conj (completedRiemannZeta₀ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
    rw [starRingEnd_apply]
  simpa [hs, hs2] using completedRiemannZeta₀_star s

/-- Conjugation symmetry of completedRiemannZeta. -/
theorem completedRiemannZeta_conj' (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  -- completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq]
  rw [map_sub, map_sub, completedRiemannZeta₀_conj]
  simp only [map_div₀, map_one, map_sub]

end
