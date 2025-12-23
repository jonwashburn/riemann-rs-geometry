/-
# Route 3′ (Connes): determinant approximants → Hurwitz gate → RH (typed skeleton)

Connes–Consani–Moscovici (`arXiv:2511.22755`) propose an alternate Route‑3′ program:

- build approximant entire functions (from finite-prime / finite-rank operator data) whose zeros
  lie on the *real axis* in the spectral parameter `t`,
- prove locally-uniform convergence (on closed substrips of `|Im(t)| < 1/2`) to Riemann’s
  `Ξ(t) = ξ(1/2 + i t)`,
- apply a Hurwitz-type nonvanishing principle to deduce that `Ξ` has no zeros off the real axis
  in the strip, hence RH.

This file turns that narrative into a Lean-facing “assumption bundle” that plugs into:

- `ExplicitFormula/HurwitzGate.lean` for the Hurwitz step,
- `ExplicitFormula/Lagarias.lean` for the concrete completed `ξ` (`xiLagarias`).

We keep the genuinely hard analytic steps (determinant convergence, and the final equivalence
to Mathlib's `RiemannHypothesis`) as explicit named assumptions, so they can be tracked and
replaced later.
-/

import RiemannRecognitionGeometry.ExplicitFormula.HurwitzGate
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex Filter Set

/-- Riemann’s `Ξ(t) = ξ(1/2 + i t)` using Lagarias’ completed `ξ`. -/
def riemannXi (t : ℂ) : ℂ :=
  xiLagarias (1 / 2 + Complex.I * t)

/--
Connes Route‑3′ convergence assumptions, phrased exactly in the shape needed by the Hurwitz gate:

we have approximants `F n` that are holomorphic and zero-free off the real axis in the strip
`|Im(t)| < 1/2`, and converge locally uniformly to `Ξ`.
-/
structure ConnesHurwitzAssumptions where
  gate : HurwitzOffRealAxisInStripGate (f := riemannXi)

namespace ConnesHurwitzAssumptions

theorem xi_zeroFree_offRealAxis_inStrip (A : ConnesHurwitzAssumptions) :
    ZeroFreeOffRealAxisInStrip riemannXi :=
  HurwitzOffRealAxisInStripGate.zeroFree_offRealAxisInStrip (ConnesHurwitzAssumptions.gate A)

end ConnesHurwitzAssumptions

/-!
## Final step to RH (still external)

To go from “`Ξ` has no zeros off the real axis in `|Im|<1/2`” to Mathlib's `RiemannHypothesis`,
one needs the (classical) equivalence between:

- nontrivial zeros of `ζ(s)` lying on `Re(s)=1/2`, and
- zeros of `Ξ(t)=ξ(1/2+it)` in the strip `|Im(t)|<1/2` lying on the real axis.

This is standard analytic-number-theory glue, but we keep it as an explicit target lemma for now.
-/

namespace ConnesHurwitzGlue

open scoped BigOperators Nat
open Real

/-!
### Auxiliary facts: Bernoulli even-index nonvanishing (via ζ(2k) values)

We use Mathlib’s formula `hasSum_zeta_nat` (critical values) to show `bernoulli (2k) ≠ 0` for `k ≠ 0`.
This is only needed to rule out spurious zeros at negative odd integers when proving the “Ξ-strip” glue.
-/

private lemma bernoulli_two_mul_ne_zero (k : ℕ) (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 := by
  classical
  -- Let `f n = 1 / n^(2k)` (with the convention `1/0 = 0` in `ℝ`).
  let f : ℕ → ℝ := fun n : ℕ => 1 / (n : ℝ) ^ (2 * k)
  have hsum := (hasSum_zeta_nat (k := k) hk)
  have hsummable : Summable f := by
    -- `HasSum` implies `Summable`.
    simpa [f] using hsum.summable
  have hnonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    -- `0 ≤ 1 / n^(2k)` for all `n`.
    simp [f]
  have hle : f 1 ≤ ∑' n : ℕ, f n := by
    -- Single term ≤ total sum for a nonnegative summable series.
    have :=
      sum_le_tsum (s := ({1} : Finset ℕ)) (f := f)
        (fun n _hn => hnonneg n) hsummable
    simpa [Finset.sum_singleton] using this
  have hpos : 0 < ∑' n : ℕ, f n := by
    have h1 : 0 < f 1 := by
      -- `f 1 = 1`.
      simp [f]
    exact lt_of_lt_of_le h1 hle
  -- Rewrite the sum using the explicit formula.
  have htsum :
      (∑' n : ℕ, f n) =
        ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
              bernoulli (2 * k) / (2 * k)!) := by
    simpa [f] using hsum.tsum_eq
  have hRHS_ne_zero :
      ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
            bernoulli (2 * k) / (2 * k)!) ≠ 0 := by
    have : 0 <
        ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
              bernoulli (2 * k) / (2 * k)!) := by
      simpa [htsum] using hpos
    exact ne_of_gt this
  -- If `bernoulli (2k) = 0`, the RHS is zero, contradiction.
  intro hb
  apply hRHS_ne_zero
  simp [hb]

/-!
### Auxiliary fact: ζ has no zeros on the negative real axis except the trivial ones

We only need a narrow slice:
if `s = -n` with `n` odd, then `ζ(s) ≠ 0`.
-/

private lemma riemannZeta_neg_nat_ne_zero_of_odd {n : ℕ} (hn : Odd n) :
    riemannZeta (-(n : ℂ)) ≠ 0 := by
  -- Use the Bernoulli formula for ζ(-n).
  have hEq := riemannZeta_neg_nat_eq_bernoulli (k := n)
  -- Show the RHS is nonzero by showing `bernoulli (n+1) ≠ 0`.
  have hbernoulli_ne : bernoulli (n + 1) ≠ 0 := by
    -- `n` odd ⇒ `n+1` even ⇒ `n+1 = 2*k` with `k ≠ 0`.
    have hEven : Even (n + 1) := hn.add_one
    rcases hEven with ⟨k, hk⟩
    have hk0 : k ≠ 0 := by
      intro hk0
      -- then `n+1 = 0`, impossible
      have : n + 1 = 0 := by simpa [hk0] using hk
      exact Nat.succ_ne_zero n this
    -- Rewrite and apply `bernoulli_two_mul_ne_zero`.
    -- `hk : n+1 = 2*k` so `bernoulli (n+1) = bernoulli (2*k)`.
    -- We use `2*k` as `2*k = 2*k` (and commutativity is not needed).
    -- `bernoulli_two_mul_ne_zero` is stated for `2*k`.
    have hk' : n + 1 = 2 * k := by simpa [two_mul] using hk
    -- Rewrite and apply `bernoulli_two_mul_ne_zero`.
    simpa [hk', two_mul] using (bernoulli_two_mul_ne_zero (k := k) hk0)
  -- Now conclude ζ(-n) ≠ 0.
  -- From `ζ(-n) = (-1)^n * bernoulli(n+1)/(n+1)`, it suffices to show `bernoulli(n+1) ≠ 0`.
  intro hz
  -- Rewrite using the Bernoulli formula.
  have : ((-1 : ℂ) ^ n * bernoulli (n + 1) / (n + 1) : ℂ) = 0 := by
    simpa [hEq] using hz
  -- Clear the nonzero scalar factors.
  have hpow : ((-1 : ℂ) ^ n) ≠ 0 := by
    exact pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)
  have hden : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
  -- Clear the denominator using `div_eq_zero_iff` and `hden`.
  have : ((-1 : ℂ) ^ n * (bernoulli (n + 1) : ℂ)) = 0 := by
    have hdiv : ((-1 : ℂ) ^ n * bernoulli (n + 1) / (n + 1) : ℂ) = 0 := this
    rcases (div_eq_zero_iff).1 hdiv with hnum | hden0
    · simpa [mul_assoc] using hnum
    ·
      -- `hden0` is the simplified form `((n:ℂ)+1)=0`; rewrite it back to `((n+1:ℕ):ℂ)=0`.
      have hden0' : ((n + 1 : ℕ) : ℂ) = 0 := by
        simpa using hden0
      exact (hden hden0').elim
  rcases mul_eq_zero.mp this with hpow0 | hbern0
  · exact False.elim (hpow hpow0)
  · -- `bernoulli (n+1) = 0`, contradiction
    have : bernoulli (n + 1) = 0 :=
      Rat.cast_injective (α := ℂ) (by simpa using hbern0)
    exact hbernoulli_ne this

/-!
### Main glue lemma: Ξ-strip zero-freeness ⇒ Mathlib RH
-/

theorem riemannHypothesis_of_xi_zeroFree_offRealAxis_inStrip
    (hXi : ZeroFreeOffRealAxisInStrip riemannXi) :
    RiemannHypothesis := by
  intro s hs0 htriv hs1
  classical

  -- First: `s.re < 1` (since ζ has no zeros on `re(s) ≥ 1`).
  have hs_lt_one : s.re < 1 := by
    by_contra hge
    have hs_ge_one : 1 ≤ s.re := le_of_not_gt hge
    exact (riemannZeta_ne_zero_of_one_le_re (s := s) hs_ge_one) hs0

  -- Second: `0 < s.re` (no zeros on `re(s) ≤ 0` except the trivial ones).
  have hs_pos : 0 < s.re := by
    by_contra hpos
    have hs_le_zero : s.re ≤ 0 := le_of_not_gt hpos
    -- Split on whether `s` is a negative integer.
    by_cases hNegInt : ∃ n : ℕ, s = -(n : ℂ)
    · rcases hNegInt with ⟨n, rfl⟩
      -- Exclude `n = 0` using ζ(0) ≠ 0.
      have hn0 : n ≠ 0 := by
        intro hn0
        subst hn0
        -- ζ(0) = -1/2
        have : riemannZeta (0 : ℂ) ≠ 0 := by
          simpa [riemannZeta_zero] using (show (- (1 / 2 : ℂ)) ≠ 0 by norm_num)
        exact this (by simpa using hs0)
      -- If `n` were even and `n ≥ 2`, it would be a trivial zero; `htriv` forbids this, hence `n` is odd.
      have hn_odd : Odd n := by
        -- `n` is not of the form `2*(k+1)` by `htriv`.
        have hnot : ¬ ∃ k : ℕ, (-(n : ℂ)) = -2 * (k + 1) := by
          -- rewrite `htriv` at `s = -n`
          simpa using htriv
        -- If `n` is even, write `n = 2*m`. Since `n ≠ 0`, we have `m+1` form unless `m=0` (i.e. `n=0`).
        -- We already excluded `n=0`, so evenness would contradict `hnot`.
        by_contra hodd
        have hEven : Even n := Nat.not_odd_iff_even.mp hodd
        rcases hEven with ⟨m, hm⟩
        cases m with
        | zero =>
            -- then n = 0, contradiction
            have : n = 0 := by simpa using hm
            exact hn0 this
        | succ m =>
            -- n = 2*(m+1) contradicts `hnot`
            have : ∃ k : ℕ, (-(n : ℂ)) = -2 * (k + 1) := by
              refine ⟨m, ?_⟩
              -- rewrite `n` and simplify
              -- `hm : n = (m+1)+(m+1) = 2*(m+1)`
              have hn2 : n = 2 * (Nat.succ m) := by
                -- `2*(m+1) = (m+1)+(m+1)`
                simpa [two_mul, Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using hm
              -- so `-(n:ℂ) = -2 * (m+1)`
              simpa [hn2, Nat.succ_eq_add_one, mul_assoc, mul_left_comm, mul_comm]
            exact hnot this
      -- Now use the Bernoulli formula to contradict `hs0`.
      exact (riemannZeta_neg_nat_ne_zero_of_odd (n := n) hn_odd) (by simpa using hs0)
    · -- Non-integer case: use the ζ functional equation to reflect to `re ≥ 1`, contradiction.
      have hs_not_neg_nat : ∀ n : ℕ, s ≠ -n := by
        intro n hn
        exact hNegInt ⟨n, hn⟩
      have hFE := riemannZeta_one_sub (s := s) hs_not_neg_nat hs1
      have hz1 : riemannZeta (1 - s) = 0 := by
        -- RHS is a product with ζ(s)=0.
        simpa [hs0] using hFE
      have hRe : 1 ≤ (1 - s).re := by
        -- `(1 - s).re = 1 - s.re ≥ 1` since `s.re ≤ 0`.
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      exact (riemannZeta_ne_zero_of_one_le_re (s := (1 - s)) hRe) hz1

  -- Convert ζ(s)=0 to ξ(s)=0 (since `0 < re(s)` ensures no gamma pole interference).
  have hs_ne0 : s ≠ 0 := by
    intro hs0'
    subst hs0'
    -- ζ(0) = -1/2
    have : riemannZeta (0 : ℂ) ≠ 0 := by
      simpa [riemannZeta_zero] using (show (- (1 / 2 : ℂ)) ≠ 0 by norm_num)
    exact this hs0
  have hxi0 : xiLagarias s = 0 :=
    xiLagarias_eq_zero_of_riemannZeta_eq_zero (s := s) (hs0 := hs_ne0) (hsre := hs_pos) hs0

  -- Now translate to the `t`-variable: `t = -I*(s-1/2)` satisfies `Ξ(t) = ξ(s)`.
  let t : ℂ := -Complex.I * (s - 1 / 2)
  have hXi_eq : riemannXi t = xiLagarias s := by
    -- `1/2 + I*t = s`
    have : (1 / 2 : ℂ) + Complex.I * t = s := by
      -- unfold `t` and simplify
      -- `t = -I*(s-1/2)` so `I*t = s-1/2`
      have : Complex.I * t = s - (1 / 2 : ℂ) := by
        -- Expand and simplify using `I*I = -1`.
        -- We do this in two small algebraic steps to avoid simp-associativity issues.
        have hII : -(Complex.I * (Complex.I * (s - (1 / 2 : ℂ)))) = s - (1 / 2 : ℂ) := by
          -- `-(I*(I*x)) = x`
          calc
            -(Complex.I * (Complex.I * (s - (1 / 2 : ℂ))))
                = -((Complex.I * Complex.I) * (s - (1 / 2 : ℂ))) := by
                    -- reassociate `I*(I*x)` to `(I*I)*x`
                    simpa [mul_assoc] using congrArg (fun z : ℂ => -z) (mul_assoc Complex.I Complex.I _).symm
            _ = -((-1 : ℂ) * (s - (1 / 2 : ℂ))) := by simp [Complex.I_mul_I]
            _ = s - (1 / 2 : ℂ) := by ring
        -- Now `I*t = s-1/2` by unfolding `t` and using `hII`.
        simpa [t, mul_assoc, sub_eq_add_neg] using hII
      -- add `1/2` on the left
      calc
        (1 / 2 : ℂ) + Complex.I * t = (1 / 2 : ℂ) + (s - (1 / 2 : ℂ)) := by simpa [this]
        _ = s := by ring
    -- `riemannXi t = xiLagarias (1/2 + I*t)` and `this : 1/2 + I*t = s`.
    simpa [riemannXi] using congrArg xiLagarias this
  have hXi0 : riemannXi t = 0 := by
    simpa [hXi_eq] using hxi0

  -- If `s.re ≠ 1/2`, then `t` lies in `upperStrip` or `lowerStrip` (since `0 < s.re < 1`),
  -- contradicting the assumed zero-freeness of `Ξ` off the real axis.
  by_contra hscrit
  have hlt_or_hgt : s.re < (1 / 2 : ℝ) ∨ (1 / 2 : ℝ) < s.re :=
    lt_or_gt_of_ne hscrit
  have ht_im : t.im = (1 / 2 : ℝ) - s.re := by
    -- compute imaginary part of `t = -I*(s-1/2)`
    -- use `mul_im` formula: `(z*w).im = z.re*w.im + z.im*w.re`
    simp [t, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, sub_re, sub_im]
  cases hlt_or_hgt with
  | inl hlt =>
      -- upper strip case
      have htU : t ∈ upperStrip := by
        have ht_im_pos : 0 < t.im := by
          -- `t.im = 1/2 - s.re`
          linarith [ht_im, hlt]
        have ht_im_lt : t.im < (1 / 2 : ℝ) := by
          -- `t.im < 1/2` since `s.re > 0`
          linarith [ht_im, hs_pos]
        exact ⟨ht_im_pos, ht_im_lt⟩
      have hNZ : riemannXi t ≠ 0 := (hXi.1 t htU)
      exact hNZ hXi0
  | inr hgt =>
      -- lower strip case
      have htL : t ∈ lowerStrip := by
        have ht_im_neg : t.im < 0 := by
          linarith [ht_im, hgt]
        have ht_im_gt : (- (1 / 2 : ℝ)) < t.im := by
          -- `-1/2 < 1/2 - s.re` since `s.re < 1`
          linarith [ht_im, hs_lt_one]
        exact ⟨ht_im_gt, ht_im_neg⟩
      have hNZ : riemannXi t ≠ 0 := (hXi.2 t htL)
      exact hNZ hXi0

end ConnesHurwitzGlue

open ConnesHurwitzGlue

theorem riemannHypothesis_of_xi_zeroFree_offRealAxis_inStrip
    (hXi : ZeroFreeOffRealAxisInStrip riemannXi) :
    RiemannHypothesis :=
  ConnesHurwitzGlue.riemannHypothesis_of_xi_zeroFree_offRealAxis_inStrip (hXi := hXi)

theorem riemannHypothesis_of_connesHurwitz (A : ConnesHurwitzAssumptions) : RiemannHypothesis :=
  riemannHypothesis_of_xi_zeroFree_offRealAxis_inStrip
    (hXi := ConnesHurwitzAssumptions.xi_zeroFree_offRealAxis_inStrip A)

end ExplicitFormula
end RiemannRecognitionGeometry
