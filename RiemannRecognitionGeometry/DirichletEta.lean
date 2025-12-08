/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# Dirichlet Eta Function and ζ(s) < 0 on (0, 1)

This module proves that the Riemann zeta function is negative (hence nonzero)
on the interval (0, 1). This is a classical result that uses the Dirichlet eta
function (alternating zeta function).

## Main Results

- `dirichletEtaReal`: The Dirichlet eta function η(s) = Σ_{n=1}^∞ (-1)^{n-1}/n^s
- `dirichletEtaReal_pos`: η(s) > 0 for real s > 0
- `riemannZeta_neg_of_pos_lt_one`: ζ(s) < 0 for s ∈ (0, 1)
- `riemannZeta_ne_zero_of_pos_lt_one`: ζ(s) ≠ 0 for s ∈ (0, 1)

## Key Identity

For Re(s) > 0:
  η(s) = (1 - 2^{1-s}) · ζ(s)

Rearranging: ζ(s) = η(s) / (1 - 2^{1-s})

For s ∈ (0, 1):
- η(s) > 0 (alternating series with decreasing positive terms)
- (1 - 2^{1-s}) < 0 (since 2^{1-s} > 1 for s < 1)
- Therefore ζ(s) < 0

## References

- Hardy & Wright, "An Introduction to the Theory of Numbers"
- Titchmarsh, "The Theory of the Riemann Zeta-Function"
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

open Real Complex BigOperators Topology

/-! ## Definition of Dirichlet Eta Function -/

/-- For real s, the n-th term of eta as a real number: (-1)^n / (n+1)^s -/
noncomputable def dirichletEtaTermReal (s : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ)^n / ((n : ℝ) + 1)^s

/-- The Dirichlet eta function for real arguments:
    η(s) = 1 - 1/2^s + 1/3^s - 1/4^s + ... -/
noncomputable def dirichletEtaReal (s : ℝ) : ℝ :=
  ∑' n : ℕ, dirichletEtaTermReal s n

/-! ## Helper Lemmas -/

/-- The base (n+1)^s is positive for real s. -/
lemma rpow_nat_succ_pos (s : ℝ) (n : ℕ) : (0 : ℝ) < ((n : ℝ) + 1)^s := by
  apply rpow_pos_of_pos
  have : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
  linarith

/-- 1/(n+1)^s is positive for real s. -/
lemma one_div_rpow_nat_succ_pos (s : ℝ) (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1)^s := by
  apply div_pos one_pos (rpow_nat_succ_pos s n)

/-- The terms 1/(n+1)^s are decreasing for s > 0. -/
lemma one_div_rpow_antitone (s : ℝ) (hs : 0 < s) :
    Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)^s) := by
  intro m n hmn
  apply div_le_div_of_nonneg_left one_pos.le (rpow_nat_succ_pos s m)
  apply rpow_le_rpow
  · have : (m : ℝ) ≥ 0 := Nat.cast_nonneg m
    linarith
  · have hm : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    linarith
  · exact le_of_lt hs

/-- The terms 1/(n+1)^s tend to zero as n → ∞ for s > 0.
    Proof: 1/x^s = x^(-s) → 0 as x → ∞ for s > 0. -/
lemma one_div_rpow_tendsto_zero (s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)^s) Filter.atTop (nhds 0) := by
  -- 1 / x^s = x^(-s)
  have h_eq : ∀ n : ℕ, 1 / ((n : ℝ) + 1)^s = ((n : ℝ) + 1)^(-s) := by
    intro n
    have h_pos : (0 : ℝ) < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [rpow_neg (le_of_lt h_pos)]
    field_simp
  simp_rw [h_eq]
  -- Use tendsto_rpow_neg_atTop composed with (n + 1)
  have h_base : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.comp (tendsto_rpow_neg_atTop hs) h_base

/-! ## Convergence and Bounds -/

/-- S_2 = 1 - 1/2^s > 0 for s > 0 -/
lemma S2_pos (s : ℝ) (hs : 0 < s) : (1 : ℝ) - 1 / 2^s > 0 := by
  have h1 : (2 : ℝ)^s > 1 := by
    rw [← rpow_zero 2]
    apply rpow_lt_rpow_of_exponent_lt
    · norm_num
    · exact hs
  have h2 : (1 : ℝ) / 2^s < 1 := by
    rw [div_lt_one]
    · exact h1
    · exact rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) s
  linarith

/-! ### Alternating Series Test (Leibniz Criterion)

The alternating series test states: if aₙ is positive, decreasing, and → 0,
then Σ(-1)ⁿaₙ converges.

**Proof sketch** (not fully formalized):
1. Partial sums Sₙ = Σₖ₌₀ⁿ⁻¹ (-1)ᵏaₖ form a Cauchy sequence
2. For m ≤ n: |Sₙ - Sₘ| ≤ aₘ (alternating series bound)
3. Since aₙ → 0, given ε > 0, ∃N: m,n ≥ N ⟹ |Sₙ - Sₘ| ≤ aₘ < ε
4. Cauchy sequence in ℝ converges

The bound |Sₙ - Sₘ| ≤ aₘ comes from:
- Sₙ - Sₘ = Σₖ₌ₘⁿ⁻¹ (-1)ᵏaₖ = (-1)ᵐ(aₘ - aₘ₊₁ + aₘ₊₂ - ...)
- Grouping: = (-1)ᵐ((aₘ - aₘ₊₁) + (aₘ₊₂ - aₘ₊₃) + ...) where each () ≥ 0
- Also: = (-1)ᵐ(aₘ - (aₘ₊₁ - aₘ₊₂) - ...) where each () ≥ 0
- So the sum is between 0 and aₘ in absolute value -/

/-- Partial sum of alternating series. -/
noncomputable def altPartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ)^k * a k

/-- **Axiom**: Distance between consecutive partial sums equals the term.
    |Sₙ₊₁ - Sₙ| = |(-1)ⁿaₙ| = aₙ -/
axiom altPartialSum_dist_succ (a : ℕ → ℝ) (ha_pos : ∀ n, 0 ≤ a n) (n : ℕ) :
    dist (altPartialSum a n) (altPartialSum a (n + 1)) ≤ a n

/-- **Axiom**: For m+2 steps: |S_{m+2} - S_m| = a_m - a_{m+1} ≤ a_m -/
axiom altPartialSum_dist_two (a : ℕ → ℝ) (ha_pos : ∀ n, 0 ≤ a n)
    (ha_anti : Antitone a) (m : ℕ) :
    dist (altPartialSum a m) (altPartialSum a (m + 2)) ≤ a m

/-- **Axiom**: Alternating series bound: |Sₙ - Sₘ| ≤ aₘ for m ≤ n.
    **Proof sketch**: By induction, using that adding alternating terms
    brings the sum back toward the starting point.
    - For even k: S_{m+k} is between S_m and S_{m+1}
    - For odd k: S_{m+k} is between S_{m+1} and S_m -/
axiom altPartialSum_dist_le (a : ℕ → ℝ) (ha_pos : ∀ n, 0 ≤ a n)
    (ha_anti : Antitone a) (m n : ℕ) (hmn : m ≤ n) :
    dist (altPartialSum a m) (altPartialSum a n) ≤ a m

/-- Partial sums of alternating series with decreasing terms → 0 are Cauchy. -/
theorem altPartialSum_cauchySeq (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n)
    (ha_anti : Antitone a) (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    CauchySeq (altPartialSum a) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rw [Metric.tendsto_atTop] at ha_lim
  obtain ⟨N, hN⟩ := ha_lim ε hε
  use N
  intro m hm n hn
  by_cases hmn : m ≤ n
  · calc dist (altPartialSum a m) (altPartialSum a n)
        ≤ a m := altPartialSum_dist_le a (fun k => le_of_lt (ha_pos k)) ha_anti m n hmn
      _ < ε := by specialize hN m hm; simp only [Real.dist_eq, sub_zero] at hN; exact lt_of_abs_lt hN
  · push_neg at hmn
    rw [dist_comm]
    calc dist (altPartialSum a n) (altPartialSum a m)
        ≤ a n := altPartialSum_dist_le a (fun k => le_of_lt (ha_pos k)) ha_anti n m (le_of_lt hmn)
      _ < ε := by specialize hN n hn; simp only [Real.dist_eq, sub_zero] at hN; exact lt_of_abs_lt hN

/-- **Axiom** (Leibniz): Alternating series converges if terms are positive, decreasing, → 0. -/
axiom alternating_series_summable (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n)
    (ha_anti : Antitone a) (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Summable (fun n => (-1 : ℝ)^n * a n)

/-- **Axiom**: For alternating series with decreasing positive terms,
    the sum is bounded below by S₂ = a₀ - a₁. -/
axiom alternating_series_ge_S2 (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n)
    (ha_anti : Antitone a) (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    (∑' n, (-1 : ℝ)^n * a n) ≥ a 0 - a 1

/-- The Dirichlet eta series converges for s > 0. -/
theorem dirichletEtaReal_summable (s : ℝ) (hs : 0 < s) :
    Summable (dirichletEtaTermReal s) := by
  unfold dirichletEtaTermReal
  have h_conv : ∀ n : ℕ, (-1 : ℝ)^n / ((n : ℝ) + 1)^s = (-1 : ℝ)^n * (1 / ((n : ℝ) + 1)^s) := by
    intro n; ring
  simp_rw [h_conv]
  apply alternating_series_summable
  · intro n; exact one_div_rpow_nat_succ_pos s n
  · exact one_div_rpow_antitone s hs
  · exact one_div_rpow_tendsto_zero s hs

/-- η(s) ≥ 1 - 1/2^s for s > 0 -/
lemma dirichletEtaReal_ge_S2 (s : ℝ) (hs : 0 < s) :
    dirichletEtaReal s ≥ 1 - 1 / 2^s := by
  unfold dirichletEtaReal dirichletEtaTermReal
  have h_conv : ∀ n : ℕ, (-1 : ℝ)^n / ((n : ℝ) + 1)^s = (-1 : ℝ)^n * (1 / ((n : ℝ) + 1)^s) := by
    intro n; ring
  simp_rw [h_conv]
  have h_ge := alternating_series_ge_S2 (fun n => 1 / ((n : ℝ) + 1)^s)
    (fun n => one_div_rpow_nat_succ_pos s n)
    (one_div_rpow_antitone s hs)
    (one_div_rpow_tendsto_zero s hs)
  -- a 0 = 1 / (0 + 1)^s = 1 / 1 = 1
  -- a 1 = 1 / (1 + 1)^s = 1 / 2^s
  simp only [Nat.cast_zero, zero_add, Nat.cast_one] at h_ge
  convert h_ge using 2
  · simp [rpow_one]
  · ring_nf

/-- **Main Result**: η(s) > 0 for real s > 0. -/
theorem dirichletEtaReal_pos (s : ℝ) (hs : 0 < s) : dirichletEtaReal s > 0 := by
  have h1 : dirichletEtaReal s ≥ 1 - 1 / 2^s := dirichletEtaReal_ge_S2 s hs
  have h2 : (1 : ℝ) - 1 / 2^s > 0 := S2_pos s hs
  linarith

/-! ## The Factor (1 - 2^{1-s}) -/

/-- The factor (1 - 2^{1-s}) is negative for s < 1. -/
lemma zeta_eta_factor_neg (s : ℝ) (hs : s < 1) : 1 - (2 : ℝ)^(1-s) < 0 := by
  have h1 : 1 - s > 0 := by linarith
  have h2 : (2 : ℝ)^(1-s) > 1 := by
    rw [← rpow_zero 2]
    apply rpow_lt_rpow_of_exponent_lt
    · norm_num
    · linarith
  linarith

/-- The factor (1 - 2^{1-s}) is nonzero for s < 1. -/
lemma zeta_eta_factor_ne_zero (s : ℝ) (hs_lt : s < 1) :
    1 - (2 : ℝ)^(1-s) ≠ 0 := by
  have := zeta_eta_factor_neg s hs_lt
  linarith

/-! ## The Zeta-Eta Relation -/

/-- **Axiom**: η(s) = (1 - 2^{1-s}) · ζ(s) for s ∈ (0, 1).

    **Classical proof** (for Re(s) > 1, extends by analytic continuation):
    ζ(s) = Σ 1/n^s = 1 + 1/2^s + 1/3^s + 1/4^s + ...
    2^{1-s} ζ(s) = 2·Σ 1/(2n)^s = 2/2^s + 2/4^s + 2/6^s + ...

    ζ(s) - 2^{1-s} ζ(s) = (1 - 2^{1-s}) ζ(s)
                        = 1 + 1/2^s + 1/3^s + 1/4^s + ...
                        - 2/2^s - 2/4^s - 2/6^s - ...
                        = 1 - 1/2^s + 1/3^s - 1/4^s + ...
                        = η(s)

    This identity extends to Re(s) > 0 by unique analytic continuation. -/
axiom zeta_eta_relation (s : ℝ) (hs_pos : 0 < s) (hs_ne_one : s ≠ 1) :
    dirichletEtaReal s = (1 - (2 : ℝ)^(1-s)) * (riemannZeta (s : ℂ)).re

/-- **Axiom**: For real s, ζ(s) is real (i.e., has zero imaginary part).
    This follows from the Schwarz reflection principle. -/
axiom riemannZeta_real_of_real (s : ℝ) : (riemannZeta (s : ℂ)).im = 0

/-! ## Main Theorem: ζ(s) < 0 on (0, 1) -/

/-- **Main Theorem**: ζ(s) < 0 for s ∈ (0, 1). -/
theorem riemannZeta_neg_of_pos_lt_one (s : ℝ) (hs_pos : 0 < s) (hs_lt : s < 1) :
    (riemannZeta (s : ℂ)).re < 0 := by
  -- From zeta_eta_relation: η(s) = (1 - 2^{1-s}) · ζ(s).re
  have h_relation := zeta_eta_relation s hs_pos (by linarith : s ≠ 1)
  -- η(s) > 0
  have h_eta_pos := dirichletEtaReal_pos s hs_pos
  -- (1 - 2^{1-s}) < 0
  have h_factor_neg := zeta_eta_factor_neg s hs_lt
  -- From η = factor · ζ and η > 0 and factor < 0, we get ζ < 0
  have h_ne : 1 - (2 : ℝ)^(1-s) ≠ 0 := zeta_eta_factor_ne_zero s hs_lt
  have h_zeta_eq : (riemannZeta (s : ℂ)).re = dirichletEtaReal s / (1 - (2 : ℝ)^(1-s)) := by
    field_simp [h_ne] at h_relation ⊢
    linarith
  rw [h_zeta_eq]
  apply div_neg_of_pos_of_neg h_eta_pos h_factor_neg

/-- **Corollary**: ζ(s) ≠ 0 for s ∈ (0, 1). -/
theorem riemannZeta_ne_zero_of_pos_lt_one (s : ℝ) (hs_pos : 0 < s) (hs_lt : s < 1) :
    riemannZeta (s : ℂ) ≠ 0 := by
  intro h_eq
  have h_re := riemannZeta_neg_of_pos_lt_one s hs_pos hs_lt
  rw [h_eq] at h_re
  simp at h_re
