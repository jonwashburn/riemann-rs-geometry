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

## Important Note on Convergence

Alternating series are **conditionally convergent**, not absolutely convergent.
This means they are NOT `Summable` in the Mathlib sense (which requires
unconditional convergence). We define η(s) as the limit of ordered partial
sums, which is guaranteed to exist by Mathlib's alternating series test.

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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Logic.Equiv.Nat

open Real Complex BigOperators Topology

/-! ## Helper Lemmas for Powers -/

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

/-! ## Alternating Series Theory -/

/-- Partial sum of alternating series. -/
noncomputable def altPartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ)^k * a k

/-- Distance between consecutive partial sums equals the term.
    Sₙ₊₁ - Sₙ = (-1)ⁿaₙ, so |Sₙ₊₁ - Sₙ| = |(-1)ⁿ||aₙ| = aₙ -/
theorem altPartialSum_dist_succ (a : ℕ → ℝ) (ha_pos : ∀ n, 0 ≤ a n) (n : ℕ) :
    dist (altPartialSum a n) (altPartialSum a (n + 1)) ≤ a n := by
  unfold altPartialSum
  rw [Finset.sum_range_succ, Real.dist_eq]
  -- Goal: |Sₙ - (Sₙ + (-1)^n * a_n)| ≤ a_n
  have h_simp : (∑ k ∈ Finset.range n, (-1 : ℝ)^k * a k) -
                (∑ k ∈ Finset.range n, (-1 : ℝ)^k * a k + (-1)^n * a n)
              = -((-1 : ℝ)^n * a n) := by ring
  rw [h_simp, abs_neg, abs_mul]
  have h_sign : (|(-1 : ℝ)^n| : ℝ) = 1 := by
    rw [_root_.abs_pow, abs_neg, abs_one, one_pow]
  rw [h_sign, one_mul, _root_.abs_of_nonneg (ha_pos n)]

/-- For m+2 steps: S_{m+2} - S_m = (-1)^m(a_m - a_{m+1}), so |S_{m+2} - S_m| = a_m - a_{m+1} ≤ a_m -/
theorem altPartialSum_dist_two (a : ℕ → ℝ) (ha_pos : ∀ n, 0 ≤ a n)
    (ha_anti : Antitone a) (m : ℕ) :
    dist (altPartialSum a m) (altPartialSum a (m + 2)) ≤ a m := by
  unfold altPartialSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Real.dist_eq]
  have h : (∑ k ∈ Finset.range m, (-1 : ℝ)^k * a k) -
          (∑ k ∈ Finset.range m, (-1 : ℝ)^k * a k + (-1)^m * a m + (-1)^(m+1) * a (m+1))
          = -((-1)^m * (a m - a (m+1))) := by rw [pow_succ]; ring
  rw [h, abs_neg, abs_mul]
  have h_sign : (|(-1 : ℝ)^m| : ℝ) = 1 := by
    rw [_root_.abs_pow, abs_neg, abs_one, one_pow]
  rw [h_sign, one_mul]
  have h_le : a (m + 1) ≤ a m := ha_anti (Nat.le_succ m)
  rw [_root_.abs_of_nonneg (by linarith : 0 ≤ a m - a (m + 1))]
  linarith [ha_pos (m + 1)]

private lemma neg_one_pow_even' (j : ℕ) : (-1 : ℝ)^(2 * j) = 1 := by
  rw [pow_mul, neg_one_sq, one_pow]

private lemma neg_one_pow_odd' (j : ℕ) : (-1 : ℝ)^(2 * j + 1) = -1 := by
  rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]

/-- For even k, the signed difference is in [0, a_m - a_{m+k}]. -/
private lemma signed_diff_even (a : ℕ → ℝ) (ha_pos : ∀ n, 0 ≤ a n)
    (ha_anti : Antitone a) (m j : ℕ) :
    0 ≤ (-1 : ℝ)^m * (altPartialSum a (m + 2*j) - altPartialSum a m) ∧
    (-1 : ℝ)^m * (altPartialSum a (m + 2*j) - altPartialSum a m) ≤ a m - a (m + 2*j) := by
  induction j with
  | zero =>
    simp only [Nat.mul_zero, add_zero, sub_self, mul_zero]
    constructor <;> linarith [ha_pos m]
  | succ j ih =>
    obtain ⟨ih_lo, ih_hi⟩ := ih
    have h_step : altPartialSum a (m + 2*(j+1)) - altPartialSum a m =
                  (altPartialSum a (m + 2*j) - altPartialSum a m) +
                  (-1)^(m + 2*j) * a (m + 2*j) + (-1)^(m + 2*j + 1) * a (m + 2*j + 1) := by
      unfold altPartialSum
      have h1 : m + 2*(j+1) = (m + 2*j + 1) + 1 := by ring
      have h2 : m + 2*j + 1 = (m + 2*j) + 1 := by ring
      rw [h1, Finset.sum_range_succ, h2, Finset.sum_range_succ]; ring
    have h_pow1 : (-1 : ℝ)^m * (-1)^(m + 2*j) = 1 := by
      rw [← pow_add]; convert neg_one_pow_even' (m + j) using 1; ring
    have h_pow2 : (-1 : ℝ)^m * (-1)^(m + 2*j + 1) = -1 := by
      rw [← pow_add]; convert neg_one_pow_odd' (m + j) using 1; ring
    have h_eq : (-1 : ℝ)^m * (altPartialSum a (m + 2*(j+1)) - altPartialSum a m) =
                (-1)^m * (altPartialSum a (m + 2*j) - altPartialSum a m) + a (m + 2*j) - a (m + 2*j + 1) := by
      rw [h_step, mul_add, mul_add]
      have eq1 : (-1 : ℝ)^m * ((-1)^(m + 2*j) * a (m + 2*j)) = a (m + 2*j) := by
        rw [← mul_assoc, h_pow1, one_mul]
      have eq2 : (-1 : ℝ)^m * ((-1)^(m + 2*j + 1) * a (m + 2*j + 1)) = -a (m + 2*j + 1) := by
        rw [← mul_assoc, h_pow2, neg_one_mul]
      rw [eq1, eq2]; ring
    constructor
    · rw [h_eq]
      have h_pair : a (m + 2*j) - a (m + 2*j + 1) ≥ 0 := by
        have := ha_anti (Nat.le_succ (m + 2*j)); linarith
      linarith
    · rw [h_eq]
      have h_anti_next : a (m + 2*(j+1)) ≤ a (m + 2*j + 1) := ha_anti (by omega)
      linarith

/-- For odd k, the signed difference is in [a_{m+k}, a_m]. -/
private lemma signed_diff_odd (a : ℕ → ℝ) (ha_pos : ∀ n, 0 ≤ a n)
    (ha_anti : Antitone a) (m j : ℕ) :
    a (m + (2*j + 1)) ≤ (-1 : ℝ)^m * (altPartialSum a (m + (2*j + 1)) - altPartialSum a m) ∧
    (-1 : ℝ)^m * (altPartialSum a (m + (2*j + 1)) - altPartialSum a m) ≤ a m := by
  have ⟨h_even_lo, h_even_hi⟩ := signed_diff_even a ha_pos ha_anti m j
  have h_step : altPartialSum a (m + (2*j + 1)) - altPartialSum a m =
                (altPartialSum a (m + 2*j) - altPartialSum a m) + (-1)^(m + 2*j) * a (m + 2*j) := by
    unfold altPartialSum
    have h1 : m + (2*j + 1) = (m + 2*j) + 1 := by ring
    rw [h1, Finset.sum_range_succ]; ring
  have h_pow : (-1 : ℝ)^m * (-1)^(m + 2*j) = 1 := by
    rw [← pow_add]; convert neg_one_pow_even' (m + j) using 1; ring
  have h_eq : (-1 : ℝ)^m * (altPartialSum a (m + (2*j + 1)) - altPartialSum a m) =
              (-1)^m * (altPartialSum a (m + 2*j) - altPartialSum a m) + a (m + 2*j) := by
    rw [h_step, mul_add, ← mul_assoc, h_pow, one_mul]
  constructor
  · rw [h_eq]; have h_anti : a (m + (2*j + 1)) ≤ a (m + 2*j) := ha_anti (by omega); linarith
  · rw [h_eq]; linarith

/-- Alternating series bound: |Sₙ - Sₘ| ≤ aₘ for m ≤ n.
    This is the key lemma for proving the Leibniz alternating series test. -/
theorem altPartialSum_dist_le (a : ℕ → ℝ) (ha_pos : ∀ n, 0 ≤ a n)
    (ha_anti : Antitone a) (m n : ℕ) (hmn : m ≤ n) :
    dist (altPartialSum a m) (altPartialSum a n) ≤ a m := by
  obtain ⟨k, hk⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  subst hk; clear hmn
  rw [Real.dist_eq, abs_sub_comm]
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- k = j + j = 2*j (even case)
    subst hj
    have ⟨h_lo, h_hi⟩ := signed_diff_even a ha_pos ha_anti m j
    have h_abs : |altPartialSum a (m + (j + j)) - altPartialSum a m| =
                 |(-1 : ℝ)^m * (altPartialSum a (m + (j + j)) - altPartialSum a m)| := by
      rw [abs_mul, _root_.abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have h_jj : j + j = 2 * j := by ring
    rw [h_jj] at h_abs ⊢
    rw [h_abs, _root_.abs_of_nonneg h_lo]
    linarith [ha_pos (m + 2*j)]
  · -- k = 2*j + 1 (odd case)
    subst hj
    have ⟨h_lo, h_hi⟩ := signed_diff_odd a ha_pos ha_anti m j
    have h_abs : |altPartialSum a (m + (2*j + 1)) - altPartialSum a m| =
                 |(-1 : ℝ)^m * (altPartialSum a (m + (2*j + 1)) - altPartialSum a m)| := by
      rw [abs_mul, _root_.abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have h_nonneg : 0 ≤ (-1 : ℝ)^m * (altPartialSum a (m + (2*j + 1)) - altPartialSum a m) := by
      linarith [ha_pos (m + (2*j + 1))]
    rw [h_abs, _root_.abs_of_nonneg h_nonneg]; exact h_hi

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

/-- **Theorem** (Leibniz): Alternating series partial sums converge.

    This is Mathlib's `Antitone.tendsto_alternating_series_of_tendsto_zero` wrapped
    for our specific use case. Note: alternating series are NOT `Summable` in the
    Mathlib sense (which requires unconditional/absolute convergence), but the
    ordered partial sums DO converge.
-/
theorem alternating_series_converges (a : ℕ → ℝ) (_ha_pos : ∀ n, 0 < a n)
    (ha_anti : Antitone a) (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ l, Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (-1 : ℝ)^k * a k)
        Filter.atTop (nhds l) :=
  Antitone.tendsto_alternating_series_of_tendsto_zero ha_anti ha_lim

/-- The limit of alternating series partial sums. -/
noncomputable def alternatingSeriesLimit (a : ℕ → ℝ) (ha_anti : Antitone a)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) : ℝ :=
  Classical.choose (Antitone.tendsto_alternating_series_of_tendsto_zero ha_anti ha_lim)

/-- The partial sums converge to the alternating series limit. -/
theorem tendsto_alternatingSeriesLimit (a : ℕ → ℝ) (ha_anti : Antitone a)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (-1 : ℝ)^k * a k)
        Filter.atTop (nhds (alternatingSeriesLimit a ha_anti ha_lim)) :=
  Classical.choose_spec (Antitone.tendsto_alternating_series_of_tendsto_zero ha_anti ha_lim)

/-- **Theorem**: For alternating series with decreasing positive terms,
    the limit is bounded below by S₂ = a₀ - a₁.

    **Proof**: Use Mathlib's `Antitone.alternating_series_le_tendsto` which says
    even partial sums are lower bounds: S_{2k} ≤ limit.
    For k = 1: S_2 = a_0 - a_1 ≤ limit. -/
theorem alternating_series_ge_S2 (a : ℕ → ℝ) (_ha_pos : ∀ n, 0 < a n)
    (ha_anti : Antitone a) (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    alternatingSeriesLimit a ha_anti ha_lim ≥ a 0 - a 1 := by
  -- Get the limit and its tendsto property
  have hl := tendsto_alternatingSeriesLimit a ha_anti ha_lim
  -- Use Antitone.alternating_series_le_tendsto with k = 1
  have h_lower := Antitone.alternating_series_le_tendsto hl ha_anti 1
  -- S_2 = ∑ i ∈ range 2, (-1)^i * a i = a 0 - a 1
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton] at h_lower
  simp only [pow_zero, one_mul, pow_one, neg_one_mul] at h_lower
  linarith

/-! ## Definition of Dirichlet Eta Function -/

/-- For real s, the n-th term of eta as a real number: (-1)^n / (n+1)^s -/
noncomputable def dirichletEtaTermReal (s : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ)^n / ((n : ℝ) + 1)^s

/-- The Dirichlet eta function for real arguments:
    η(s) = 1 - 1/2^s + 1/3^s - 1/4^s + ...

    **Important**: This is defined as the limit of partial sums, NOT using tsum.
    Alternating series are conditionally convergent, not absolutely convergent,
    so they are NOT `Summable` in the Mathlib sense. We use the limit of
    ordered partial sums which is guaranteed to exist by Mathlib's
    `Antitone.tendsto_alternating_series_of_tendsto_zero`.

    For s ≤ 0, this definition returns 0 (a placeholder value since the series
    doesn't converge in this region). -/
noncomputable def dirichletEtaReal (s : ℝ) : ℝ :=
  if hs : 0 < s then
    alternatingSeriesLimit
      (fun n => 1 / ((n : ℝ) + 1)^s)
      (one_div_rpow_antitone s hs)
      (one_div_rpow_tendsto_zero s hs)
  else 0

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

/-- The Dirichlet eta series partial sums converge for s > 0. -/
theorem dirichletEtaReal_converges (s : ℝ) (hs : 0 < s) :
    ∃ l, Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, dirichletEtaTermReal s k)
        Filter.atTop (nhds l) := by
  unfold dirichletEtaTermReal
  have h_conv : ∀ n : ℕ, (-1 : ℝ)^n / ((n : ℝ) + 1)^s = (-1 : ℝ)^n * (1 / ((n : ℝ) + 1)^s) := by
    intro n; ring
  simp_rw [h_conv]
  exact alternating_series_converges _ (fun n => one_div_rpow_nat_succ_pos s n)
    (one_div_rpow_antitone s hs) (one_div_rpow_tendsto_zero s hs)

/-- The Dirichlet eta function equals the limit of partial sums. -/
theorem dirichletEtaReal_eq_limit (s : ℝ) (hs : 0 < s) :
    dirichletEtaReal s = alternatingSeriesLimit
      (fun n => 1 / ((n : ℝ) + 1)^s)
      (one_div_rpow_antitone s hs)
      (one_div_rpow_tendsto_zero s hs) := by
  simp only [dirichletEtaReal, dif_pos hs]

/-- η(s) ≥ 1 - 1/2^s for s > 0 -/
lemma dirichletEtaReal_ge_S2 (s : ℝ) (hs : 0 < s) :
    dirichletEtaReal s ≥ 1 - 1 / 2^s := by
  rw [dirichletEtaReal_eq_limit s hs]
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

/-! ## Summability for s > 1

For s > 1, both the zeta series and alternating series converge absolutely,
which allows us to use tsum manipulations. -/

/-- The series ∑ 1/(n+1)^s is summable for s > 1. -/
lemma summable_one_div_nat_succ_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)^s) := by
  have h := Real.summable_one_div_nat_add_rpow 1 s
  simp only [one_div] at h ⊢
  have h_pos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  simp_rw [abs_of_pos (h_pos _)] at h
  exact h.mpr hs

/-- The alternating series ∑ (-1)^n/(n+1)^s is absolutely summable for s > 1.
    Since |(-1)^n/(n+1)^s| = 1/(n+1)^s, absolute summability follows from
    summability of the zeta series. -/
lemma summable_alternating_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (-1 : ℝ)^n / ((n : ℝ) + 1)^s) := by
  apply Summable.of_norm
  have h_norm : ∀ n : ℕ, ‖(-1 : ℝ)^n / ((n : ℝ) + 1)^s‖ = 1 / ((n : ℝ) + 1)^s := by
    intro n
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
    have h_pos : 0 < ((n : ℝ) + 1)^s := rpow_nat_succ_pos s n
    rw [Real.norm_of_nonneg (le_of_lt h_pos), one_div]
  simp_rw [h_norm, one_div]
  have := summable_one_div_nat_succ_rpow s hs
  simp_rw [one_div] at this
  exact this

/-- For s > 1, the alternating series limit equals the tsum. -/
lemma alternatingSeriesLimit_eq_tsum (s : ℝ) (hs : 1 < s) :
    alternatingSeriesLimit
      (fun n => 1 / ((n : ℝ) + 1)^s)
      (one_div_rpow_antitone s (lt_trans zero_lt_one hs))
      (one_div_rpow_tendsto_zero s (lt_trans zero_lt_one hs)) =
    ∑' n : ℕ, (-1 : ℝ)^n / ((n : ℝ) + 1)^s := by
  -- The alternating series limit is defined via Classical.choose of the convergence
  -- For absolutely convergent series, this equals the tsum
  have h_summable := summable_alternating_rpow s hs
  have h_tendsto := tendsto_alternatingSeriesLimit
    (fun n => 1 / ((n : ℝ) + 1)^s)
    (one_div_rpow_antitone s (lt_trans zero_lt_one hs))
    (one_div_rpow_tendsto_zero s (lt_trans zero_lt_one hs))
  -- Convert partial sums to match tsum definition
  have h_eq : ∀ n, ∑ k ∈ Finset.range n, (-1 : ℝ)^k * (1 / ((k : ℝ) + 1)^s) =
              ∑ k ∈ Finset.range n, (-1 : ℝ)^k / ((k : ℝ) + 1)^s := by
    intro n; congr 1; ext k; ring
  simp_rw [h_eq] at h_tendsto
  exact tendsto_nhds_unique h_tendsto h_summable.hasSum.tendsto_sum_nat

/-- Split a tsum over ℕ into sums over even and odd indices.
    Uses `tsum_subtype_add_tsum_subtype_compl` with the set of even numbers. -/
lemma tsum_nat_eq_even_add_odd {f : ℕ → ℝ} (hf : Summable f) :
    ∑' n, f n = ∑' n, f (2 * n) + ∑' n, f (2 * n + 1) := by
  -- Split into even and odd parts using the set {n | Even n}
  have h_split := tsum_subtype_add_tsum_subtype_compl hf {n : ℕ | Even n}
  -- Rewrite the even part: ∑' (n : {n | Even n}), f n = ∑' k, f (2 * k)
  have h_even : ∑' (n : {n : ℕ | Even n}), f n = ∑' k, f (2 * k) := by
    let e : ℕ ≃ {n : ℕ | Even n} := {
      toFun := fun k => ⟨2 * k, even_two_mul k⟩
      invFun := fun ⟨n, _⟩ => n / 2
      left_inv := fun k => Nat.mul_div_cancel_left k (by norm_num : 0 < 2)
      right_inv := fun ⟨n, hn⟩ => by
        ext; exact Nat.two_mul_div_two_of_even hn
    }
    exact (Equiv.tsum_eq e (fun x => f x.1)).symm
  -- Rewrite the odd part using complement notation
  have h_odd : ∑' (n : ↑({n : ℕ | Even n}ᶜ)), f n = ∑' k, f (2 * k + 1) := by
    -- The complement of Even is Odd
    have h_compl_eq : ({n : ℕ | Even n}ᶜ : Set ℕ) = {n : ℕ | Odd n} := by
      ext n; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Nat.not_even_iff_odd]
    -- Create equivalence for the complement set directly
    let e : ℕ ≃ ↑({n : ℕ | Even n}ᶜ) := {
      toFun := fun k => ⟨2 * k + 1, by
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        exact Nat.not_even_two_mul_add_one k⟩
      invFun := fun ⟨n, _⟩ => n / 2
      left_inv := fun k => by simp only; omega
      right_inv := fun ⟨n, hn⟩ => by
        ext
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hn
        have h_odd : Odd n := Nat.odd_iff_not_even.mpr hn
        obtain ⟨k, hk⟩ := h_odd
        simp only [hk]; omega
    }
    exact (Equiv.tsum_eq e (fun x => f x.1)).symm
  -- Combine
  rw [← h_split, h_even, h_odd]

/-- The sum over even indices: ∑ 1/(2n+2)^s = 2^{-s} · ∑ 1/(n+1)^s -/
lemma tsum_even_eq_two_pow_neg_mul (s : ℝ) (hs : 1 < s) :
    ∑' n : ℕ, 1 / ((2 * n : ℝ) + 2)^s = (2 : ℝ)^(-s) * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s := by
  have h_sum := summable_one_div_nat_succ_rpow s hs
  -- Rewrite 1/(2n+2)^s = 1/(2(n+1))^s = 2^{-s}/(n+1)^s
  have h_eq : ∀ n : ℕ, 1 / ((2 * n : ℝ) + 2)^s = (2 : ℝ)^(-s) * (1 / ((n : ℝ) + 1)^s) := by
    intro n
    have h_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h_two_pos : (0 : ℝ) < 2 := by norm_num
    calc 1 / ((2 * n : ℝ) + 2)^s
        = 1 / (2 * ((n : ℝ) + 1))^s := by ring_nf
      _ = 1 / ((2 : ℝ)^s * ((n : ℝ) + 1)^s) := by rw [mul_rpow (by linarith : (0 : ℝ) ≤ 2) (le_of_lt h_pos)]
      _ = (2 : ℝ)^(-s) / ((n : ℝ) + 1)^s := by rw [rpow_neg (le_of_lt h_two_pos)]; field_simp
      _ = (2 : ℝ)^(-s) * (1 / ((n : ℝ) + 1)^s) := by ring
  simp_rw [h_eq]
  rw [tsum_mul_left]

/-- The sum over odd indices: ∑ 1/(2n+1)^s = ζ - 2^{-s}·ζ for s > 1. -/
lemma tsum_odd_eq_zeta_sub_even (s : ℝ) (hs : 1 < s) :
    ∑' n : ℕ, 1 / ((2 * n : ℝ) + 1)^s =
    (1 - (2 : ℝ)^(-s)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s := by
  have h_zeta := summable_one_div_nat_succ_rpow s hs
  have h_even := tsum_even_eq_two_pow_neg_mul s hs
  -- Use tsum_nat_eq_even_add_odd to split: ζ = (even index sum) + (odd index sum)
  have h_split := tsum_nat_eq_even_add_odd h_zeta
  -- Convert cast expressions to match: (2 * n : ℕ) → ℝ vs 2 * (n : ℝ)
  have h_cast_even : ∀ n : ℕ, ((2 * n : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 1 := by
    intro n; simp only [Nat.cast_mul, Nat.cast_ofNat]
  have h_cast_odd : ∀ n : ℕ, ((2 * n + 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 2 := by
    intro n; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]; ring
  -- Rewrite the sums in h_split
  have h_even_sum_eq : ∑' n : ℕ, 1 / (((2 * n : ℕ) : ℝ) + 1)^s = ∑' n : ℕ, 1 / (2 * (n : ℝ) + 1)^s := by
    congr 1; ext n; rw [h_cast_even]
  have h_odd_sum_eq : ∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℝ) + 1)^s = ∑' n : ℕ, 1 / (2 * (n : ℝ) + 2)^s := by
    congr 1; ext n; rw [h_cast_odd]
  rw [h_even_sum_eq, h_odd_sum_eq] at h_split
  -- h_split: ∑ 1/(n+1)^s = ∑ 1/(2n+1)^s + ∑ 1/(2n+2)^s
  -- Rearranging: ∑ 1/(2n+1)^s = ∑ 1/(n+1)^s - ∑ 1/(2n+2)^s
  have h_rearrange : ∑' n : ℕ, 1 / ((2 * n : ℝ) + 1)^s =
      ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s - ∑' n : ℕ, 1 / ((2 * n : ℝ) + 2)^s := by
    linarith
  rw [h_rearrange, h_even]
  ring

/-- Key algebraic identity: alternating sum = (1 - 2^{1-s}) · zeta sum for s > 1.
    Proof outline:
    - Let a_n = 1/(n+1)^s
    - Even-indexed terms (n=0,2,4,...): a_0, a_2, ... have odd denominators: 1, 3, 5, ...
    - Odd-indexed terms (n=1,3,5,...): a_1, a_3, ... have even denominators: 2, 4, 6, ...
    - Let E = ∑ a_{2k} (odd denominators), O = ∑ a_{2k+1} (even denominators)
    - Then ζ = E + O and η = E - O
    - We have O = 2^{-s}·ζ, so E = ζ - O = (1 - 2^{-s})·ζ
    - Therefore η = E - O = (1 - 2^{-s})·ζ - 2^{-s}·ζ = (1 - 2·2^{-s})·ζ = (1 - 2^{1-s})·ζ -/
lemma alternating_eq_factor_mul_zeta_tsum (s : ℝ) (hs : 1 < s) :
    ∑' n : ℕ, (-1 : ℝ)^n / ((n : ℝ) + 1)^s =
    (1 - (2 : ℝ)^(1-s)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s := by
  have h_zeta_sum := summable_one_div_nat_succ_rpow s hs
  have h_alt_sum := summable_alternating_rpow s hs
  have h_even := tsum_even_eq_two_pow_neg_mul s hs
  have h_odd := tsum_odd_eq_zeta_sub_even s hs
  -- Split alternating sum into even and odd indexed parts using tsum_nat_eq_even_add_odd
  have h_split := tsum_nat_eq_even_add_odd h_alt_sum
  -- For even indices: (-1)^(2k) / ((2k)+1)^s = 1 / (2k+1)^s
  have h_even_alt : ∑' k : ℕ, (-1 : ℝ)^(2*k) / (((2*k : ℕ) : ℝ) + 1)^s =
                    ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1)^s := by
    congr 1; ext k
    have h_pow : (-1 : ℝ)^(2*k) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
    simp only [h_pow, one_div, Nat.cast_mul, Nat.cast_ofNat]
  -- For odd indices: (-1)^(2k+1) / ((2k+1)+1)^s = -1 / (2k+2)^s
  have h_odd_alt : ∑' k : ℕ, (-1 : ℝ)^(2*k+1) / (((2*k+1 : ℕ) : ℝ) + 1)^s =
                   -∑' k : ℕ, 1 / (2 * (k : ℝ) + 2)^s := by
    rw [← tsum_neg]
    congr 1; ext k
    have h_pow : (-1 : ℝ)^(2*k+1) = -1 := by rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    simp only [h_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, neg_div, neg_neg]
    ring_nf
  -- Rewrite h_split to use our normalized forms
  rw [h_even_alt, h_odd_alt] at h_split
  -- Now h_split: η = E + (-O) where E = ∑ 1/(2k+1)^s and O = ∑ 1/(2k+2)^s
  -- Use h_odd: E = (1 - 2^{-s})·ζ  and  h_even: O = 2^{-s}·ζ
  rw [h_odd, h_even] at h_split
  -- h_split: η = (1 - 2^{-s})·ζ + (-(2^{-s}·ζ)) = (1 - 2^{-s} - 2^{-s})·ζ
  -- Need to show: (1 - 2^{-s} - 2^{-s})·ζ = (1 - 2^{1-s})·ζ
  have h_exp : (2 : ℝ) * 2^(-s) = 2^(1-s) := by
    have h1 : (2 : ℝ)^(1-s) = 2^(1 + (-s)) := by ring_nf
    rw [h1, rpow_add (by norm_num : (0 : ℝ) < 2), rpow_one]
  calc ∑' n : ℕ, (-1 : ℝ)^n / ((n : ℝ) + 1)^s
      = (1 - 2^(-s)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s +
        -(2^(-s) * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s) := h_split
    _ = (1 - 2^(-s) - 2^(-s)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s := by ring
    _ = (1 - 2 * 2^(-s)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s := by ring
    _ = (1 - 2^(1-s)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s := by rw [h_exp]

/-! ## The Zeta-Eta Relation

This axiom encodes the fundamental identity connecting the Dirichlet eta function
(defined as our alternating series limit) with Mathlib's `riemannZeta`.

### Progress Made

We have established the following infrastructure for s > 1:

1. ✅ `summable_one_div_nat_succ_rpow` - The zeta series is summable
2. ✅ `summable_alternating_rpow` - The alternating series is absolutely summable
3. ✅ `alternatingSeriesLimit_eq_tsum` - Our limit equals the tsum
4. ✅ `tsum_even_eq_two_pow_neg_mul` - Sum over even indices = 2^{-s} · ζ

### Remaining Step for s > 1

The key missing piece is splitting the tsum into even and odd indexed parts:
```
∑' n, a_n = ∑' k, a_{2k} + ∑' k, a_{2k+1}
```
This would allow completing `alternating_eq_factor_mul_zeta_tsum` for s > 1.

### Why the Axiom Remains

Even with s > 1 proven, extending to s ∈ (0, 1) requires:

1. **Real-complex bridge**: Show `(riemannZeta (s : ℂ)).re = ∑' n, 1/(n+1)^s`
   for real s > 1 (the complex tsum has real terms for real s)

2. **Analytic continuation**: Extend from s > 1 to s ∈ (0, 1)
   - Mathlib defines ζ(s) via Hurwitz zeta analytic continuation
   - Our η(s) is directly defined as an alternating series limit for s > 0
   - Need uniqueness of analytic continuation to connect them

### Mathematical Status

This is **Theorem 25.2** in Hardy & Wright's "An Introduction to the Theory
of Numbers" and is completely standard in analytic number theory. The identity
is a cornerstone result connecting:
- The Dirichlet eta function (alternating zeta)
- The Riemann zeta function

### Note on the Proof

The main theorem `riemannZeta_ne_zero_of_pos_lt_one` only uses
`(riemannZeta s).re`, so we don't need to separately prove that ζ(s) is
real for real s > 0 (though this is mathematically true by the Schwarz
reflection principle).
-/

/-! ## Real-Complex Bridge for Zeta Function

For real s > 1, we connect the real series ∑ 1/(n+1)^s to Mathlib's complex riemannZeta. -/

/-- For real s > 1, each term 1/(n+1)^s in the complex zeta series is real.

    This follows from Complex.ofReal_cpow: for x ≥ 0 and real s, x^s (complex) = x^s (real). -/
lemma zeta_term_real (n : ℕ) (s : ℝ) (_hs : 1 < s) :
    (1 / ((n : ℂ) + 1) ^ (s : ℂ)).re = 1 / ((n : ℝ) + 1) ^ s := by
  have h_pos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  -- Rewrite using ofReal lemmas to convert complex expression to real
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
    ← Complex.ofReal_cpow h_pos, ← Complex.ofReal_div, Complex.ofReal_re]

/-- The series ∑ 1/(n+1)^s is summable in ℂ for Re(s) > 1. -/
lemma summable_complex_zeta_series (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (s : ℂ)) := by
  have h_re : 1 < (s : ℂ).re := by simp [hs]
  -- Transform to match Mathlib's form
  have h := Complex.summable_one_div_nat_cpow.mpr h_re
  -- ∑ 1/n^s is summable ↔ ∑ 1/(n+1)^s is summable (shift by 1)
  rw [← summable_nat_add_iff 1] at h
  convert h using 1
  ext n
  simp only [one_div, Nat.cast_add, Nat.cast_one]

/-- The complex zeta series for real s > 1 has real terms that sum to a real value. -/
lemma riemannZeta_re_eq_real_tsum (s : ℝ) (hs : 1 < s) :
    (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s := by
  -- Use Mathlib's zeta_eq_tsum_one_div_nat_add_one_cpow
  have h_re : 1 < (s : ℂ).re := by simp [hs]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h_re]
  -- Use Complex.re_tsum to pull out the real part
  have h_summable := summable_complex_zeta_series s hs
  rw [Complex.re_tsum h_summable]
  congr 1
  ext n
  exact zeta_term_real n s hs

/-- **THEOREM**: The zeta-eta relation for s > 1 (proven via series manipulation).

    This connects:
    - Our `dirichletEtaReal` (defined via alternating series limit)
    - Mathlib's `riemannZeta` (defined via Hurwitz zeta analytic continuation)

    For real s > 1, both series converge absolutely, allowing direct comparison. -/
theorem zeta_eta_relation_gt_one (s : ℝ) (hs : 1 < s) :
    dirichletEtaReal s = (1 - (2 : ℝ)^(1-s)) * (riemannZeta (s : ℂ)).re := by
  -- Step 1: dirichletEtaReal s = alternatingSeriesLimit ... (by definition)
  have hs_pos : 0 < s := lt_trans zero_lt_one hs
  rw [dirichletEtaReal_eq_limit s hs_pos]
  -- Step 2: alternatingSeriesLimit = ∑' n, (-1)^n / (n+1)^s (for s > 1)
  rw [alternatingSeriesLimit_eq_tsum s hs]
  -- Step 3: ∑' n, (-1)^n / (n+1)^s = (1 - 2^{1-s}) * ∑' n, 1/(n+1)^s
  rw [alternating_eq_factor_mul_zeta_tsum s hs]
  -- Step 4: ∑' n, 1/(n+1)^s = (riemannZeta (s : ℂ)).re
  rw [← riemannZeta_re_eq_real_tsum s hs]

/-- **AXIOM**: η(s) = (1 - 2^{1-s}) · ζ(s) for s ∈ (0, 1).

    ### Status: CLASSICAL THEOREM (requires analytic continuation)

    For s > 1, this is proven as `zeta_eta_relation_gt_one` using series manipulation.

    For s ∈ (0, 1), the proof requires **analytic continuation**:

    **Step 1**: The Dirichlet eta function η(s) = ∑_{n=1}^∞ (-1)^{n-1}/n^s converges
    conditionally for all Re(s) > 0 (not just Re(s) > 1).

    **Step 2**: Both η(s) and (1 - 2^{1-s})ζ(s) are analytic on {Re(s) > 0, s ≠ 1}.
    - η(s) is analytic as an alternating Dirichlet series with convergence abscissa 0
    - (1 - 2^{1-s})ζ(s) is analytic: ζ has a pole at s=1 but (1 - 2^{1-s}) vanishes there

    **Step 3**: By `zeta_eta_relation_gt_one`, they agree on Re(s) > 1.

    **Step 4**: By the identity principle for analytic functions, they agree everywhere
    on {Re(s) > 0, s ≠ 1}.

    **Step 5**: For real s ∈ (0, 1), both sides are real:
    - `dirichletEtaReal s` is real by definition (limit of real partial sums)
    - `(riemannZeta (s : ℂ)).re` is the real part of Mathlib's zeta

    ### Why This Remains an Axiom

    Formalizing this in Lean requires:
    1. Proving the alternating series η(s) is analytic for Re(s) > 0
    2. Connecting our `dirichletEtaReal` to a complex analytic function
    3. Verifying Mathlib's `riemannZeta` via Hurwitz zeta matches the analytic continuation
    4. Applying the identity principle for complex analytic functions

    This infrastructure is not fully available in Mathlib for this specific application.

    ### References
    - Hardy & Wright, "An Introduction to the Theory of Numbers", Theorem 25.2
    - Titchmarsh, "The Theory of the Riemann Zeta-Function", Chapter 2
    - Apostol, "Introduction to Analytic Number Theory", Section 12.5 -/
axiom zeta_eta_relation_lt_one (s : ℝ) (hs_pos : 0 < s) (hs_lt : s < 1) :
    dirichletEtaReal s = (1 - (2 : ℝ)^(1-s)) * (riemannZeta (s : ℂ)).re

/-- The full zeta-eta relation: η(s) = (1 - 2^{1-s}) · ζ(s) for s ∈ (0, 1) ∪ (1, ∞). -/
theorem zeta_eta_relation (s : ℝ) (hs_pos : 0 < s) (hs_ne_one : s ≠ 1) :
    dirichletEtaReal s = (1 - (2 : ℝ)^(1-s)) * (riemannZeta (s : ℂ)).re := by
  by_cases h : s < 1
  · exact zeta_eta_relation_lt_one s hs_pos h
  · push_neg at h
    have hs_gt : 1 < s := lt_of_le_of_ne h (Ne.symm hs_ne_one)
    exact zeta_eta_relation_gt_one s hs_gt

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
