/-
# Zeta Conjugation Symmetry

Ported from `riemann-joint-new/riemann/PrimeNumberTheoremAnd/ZetaConj.lean`.

Proves that `riemannZeta (conj s) = conj (riemannZeta s)` and similar identities.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate

noncomputable section

open Complex

/-!
## Helper lemmas for conjugation of holomorphic functions
-/

/-- If f has derivative a at p, then conj ∘ f ∘ conj has derivative conj(a) at conj(p). -/
theorem hasDerivAt_conj_conj {f : ℂ → ℂ} {p a : ℂ} (hf : HasDerivAt f a p) :
    HasDerivAt (fun z ↦ conj (f (conj z))) (conj a) (conj p) := by
  rw [hasDerivAt_iff_tendsto] at hf ⊢
  have := Complex.continuous_conj.tendsto (conj p)
  rw [Complex.conj_conj] at this
  have := Filter.Tendsto.comp hf this
  convert this with z
  simp only [Complex.conj_conj, smul_eq_mul, Function.comp_apply]
  congr 1
  · congr 1
    rw [← Complex.norm_conj]
    simp
  · rw [← Complex.norm_conj]
    simp

/-- The derivative of conj ∘ f ∘ conj at conj(p) equals conj(deriv f p). -/
theorem deriv_conj_conj (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  set g := fun z ↦ conj (f (conj z))
  by_cases hf : DifferentiableAt ℂ f p
  · exact (hasDerivAt_conj_conj hf.hasDerivAt).deriv
  · by_cases hg : DifferentiableAt ℂ g (conj p)
    · have : DifferentiableAt ℂ f p := by
        convert (hasDerivAt_conj_conj hg.hasDerivAt).differentiableAt using 2 <;> simp [g]
      contradiction
    · rw [deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt hf, map_zero]

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

/-- Conjugation symmetry of riemannZeta: conj(ζ(conj s)) = ζ(s). -/
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
      set V := Complex.re ⁻¹' (Set.Ioi 1)
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
      convert (hasDerivAt_conj_conj (differentiableAt_riemannZeta hs₁').hasDerivAt).differentiableAt.differentiableWithinAt (s := U)
      rw [Complex.conj_conj]
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      exact (differentiableAt_riemannZeta hs₁).differentiableWithinAt
    · refine (?_ : IsConnected U).isPreconnected
      refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
      simp

/-- Conjugation symmetry of riemannZeta: ζ(conj s) = conj(ζ(s)). -/
theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rw [← conj_riemannZeta_conj, Complex.conj_conj]

/-- Conjugation symmetry of the derivative of riemannZeta. -/
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj, conj_riemannZeta_conj]

/-- Conjugation symmetry of the log-derivative of riemannZeta. -/
theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

/-- Conjugation symmetry of logDeriv riemannZeta. -/
theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

/-!
## Conjugation symmetry of completedRiemannZeta

We prove this using the functional equation and the Gamma function conjugation symmetry.
-/

/-- Conjugation symmetry of completedRiemannZeta. -/
theorem completedRiemannZeta_conj' (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  -- Use the definition: completedRiemannZeta s = Gammaℝ s * riemannZeta s (for s ≠ 0, 1)
  -- and the conjugation properties of each factor.
  by_cases hs0 : s = 0
  · subst hs0
    simp [completedRiemannZeta_zero]
  by_cases hs1 : s = 1
  · subst hs1
    simp [completedRiemannZeta_one]
  -- For s ≠ 0, 1, use the definition via riemannZeta
  have hconj0 : conj s ≠ 0 := by simp [hs0]
  have hconj1 : conj s ≠ 1 := (map_ne_one_iff (starRingEnd ℂ) (RingHom.injective (starRingEnd ℂ))).mpr hs1
  rw [completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta hconj0 hconj1]
  rw [completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta hs0 hs1]
  rw [map_mul, riemannZeta_conj]
  congr 1
  -- Gammaℝ (conj s) = conj (Gammaℝ s)
  -- Gammaℝ s = π^(-s/2) * Γ(s/2)
  simp only [Complex.Gammaℝ]
  rw [map_mul]
  congr 1
  · -- π^(-conj(s)/2) = conj(π^(-s/2))
    rw [map_cpow₀]
    · simp [Complex.conj_ofReal]
    · exact ofReal_ne_zero.mpr Real.pi_pos.ne'
    · intro h
      simp at h
  · -- Γ(conj(s)/2) = conj(Γ(s/2))
    rw [map_div₀, Complex.conj_ofReal]
    exact Complex.Gamma_conj (s / 2)

end

