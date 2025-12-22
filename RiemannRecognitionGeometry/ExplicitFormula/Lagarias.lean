/-
# Lagarias (2007): explicit formula and Weil positivity (Route 3 skeleton)

This file encodes the *statements* (as Lean-typed axioms/structures) of:
- Lagarias Thm 3.1 (Guinand–Weil explicit formula), and
- Lagarias Thm 3.2 (Weil positivity criterion for RH),

in the Mellin-transform normalization used in `renormalized_tail_bound.md` §8.

No Carleson/BMO/Whitney infrastructure is imported here.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import RiemannRecognitionGeometry.ExplicitFormula.Defs
import RiemannRecognitionGeometry.ExplicitFormula.ZetaConjugation

noncomputable section

open Complex
open scoped ComplexConjugate

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace

/-- Lagarias' completed zeta in the normalization
`ξ(s) = (1/2) s (s-1) π^{-s/2} Γ(s/2) ζ(s)`.

We define it using Mathlib's `completedRiemannZeta`:
`completedRiemannZeta s = π^{-s/2} Γ(s/2) ζ(s)` (up to harmless point-value conventions
at `s=0,1`). The prefactor `s(s-1)` removes the poles and yields an entire function.
-/
def xiLagarias (s : ℂ) : ℂ := (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s

/-!
## Basic nonvanishing on the Euler-product half-plane

These are routine glue facts used when specializing contour identities to the classical ζ-data.
-/

/-- `completedRiemannZeta` has no zeros on `Re(s) > 1` (via the Euler product for `riemannZeta`). -/
lemma completedRiemannZeta_ne_zero_of_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hΓ_ne : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < s.re)
  have hs_ne_zero : s ≠ 0 := by
    intro h
    have : (1 : ℝ) < (0 : ℝ) := by simpa [h] using hs
    linarith
  have h_def := riemannZeta_def_of_ne_zero (s := s) hs_ne_zero
  intro hΛ
  -- If `completedRiemannZeta s = 0`, then `riemannZeta s = 0` since `Gammaℝ s ≠ 0`.
  rw [h_def] at hζ_ne
  have : completedRiemannZeta s / Complex.Gammaℝ s = 0 := by simp [hΛ]
  exact hζ_ne this

/-- Lagarias' ξ is nonzero on `Re(s) > 1`. -/
lemma xiLagarias_ne_zero_of_re_gt_one {s : ℂ} (hs : 1 < s.re) : xiLagarias s ≠ 0 := by
  unfold xiLagarias
  have hhalf : (1/2 : ℂ) ≠ 0 := by norm_num
  have hs0 : s ≠ 0 := by
    intro h
    have : (1 : ℝ) < (0 : ℝ) := by simpa [h] using hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    have hs1' : s ≠ 1 := by
      intro h
      have : (1 : ℝ) < (1 : ℝ) := by simpa [h] using hs
      linarith
    exact sub_ne_zero.mpr hs1'
  have hΛ : completedRiemannZeta s ≠ 0 := completedRiemannZeta_ne_zero_of_re_gt_one (s := s) hs
  -- `xiLagarias s = (1/2) * s * (s-1) * completedRiemannZeta s`
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hhalf hs0) hs1) hΛ

lemma xiLagarias_one_sub (s : ℂ) : xiLagarias (1 - s) = xiLagarias s := by
  unfold xiLagarias
  -- First apply the functional equation to the completed zeta factor.
  rw [completedRiemannZeta_one_sub s]
  -- The remaining equality is just commutative-ring algebra in `s`.
  ring_nf

lemma deriv_xiLagarias_one_sub (s : ℂ) : deriv xiLagarias (1 - s) = - deriv xiLagarias s := by
  -- Differentiate the functional equation `xiLagarias (1 - z) = xiLagarias z`.
  have hfun : (fun z : ℂ => xiLagarias (1 - z)) = xiLagarias := by
    funext z
    simpa using xiLagarias_one_sub z
  -- Use `deriv_comp_const_sub` to compute the derivative of the left side.
  have hcomp :
      deriv (fun z : ℂ => xiLagarias (1 - z)) s = - deriv xiLagarias (1 - s) := by
    -- `1 - z` is `1 - z` (a const-sub), so this is exactly `deriv_comp_const_sub`.
    simpa [sub_eq_add_neg] using (deriv_comp_const_sub (f := xiLagarias) (a := (1 : ℂ)) (x := s))
  -- Rewrite using `hfun` and rearrange.
  have : deriv xiLagarias s = - deriv xiLagarias (1 - s) := by
    simpa [hfun] using hcomp
  -- Flip sides by negating the equality.
  have hneg : -deriv xiLagarias s = deriv xiLagarias (1 - s) := by
    simpa using congrArg (fun z : ℂ => -z) this
  simpa using hneg.symm

lemma logDeriv_xiLagarias_one_sub (s : ℂ) : logDeriv xiLagarias (1 - s) = - logDeriv xiLagarias s := by
  -- Expand `logDeriv` and rewrite using the functional equation and the derivative identity.
  -- Then it is just the algebraic identity `(-a)/b = -(a/b)`.
  simp [logDeriv, deriv_xiLagarias_one_sub, xiLagarias_one_sub, neg_div]

/-- `completedRiemannZeta` satisfies the conjugation symmetry.

This follows from:
1. `Gamma_conj`: Γ(conj s) = conj(Γ(s))
2. Real Dirichlet coefficients: ζ(conj s) = conj(ζ(s)) for Re s > 1, extended by analytic continuation
3. Real base: π^(conj s) = conj(π^s)

Proved in ZetaConjugation.lean (ported from riemann-joint-new). -/
lemma completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta s) := by
  simp only [starRingEnd_apply]
  exact completedRiemannZeta_conj' s

/-- xiLagarias satisfies the reality condition ξ(s*) = conj(ξ(s)). -/
lemma xiLagarias_conj (s : ℂ) : xiLagarias (starRingEnd ℂ s) = starRingEnd ℂ (xiLagarias s) := by
  unfold xiLagarias
  -- Use the completedRiemannZeta_conj axiom and that starRingEnd is a ring homomorphism.
  simp only [starRingEnd_apply, map_mul, map_sub, map_one, map_div₀]
  rw [← starRingEnd_apply, completedRiemannZeta_conj, starRingEnd_apply]
  -- For real numbers like 2, (starRingEnd ℂ) 2 = 2.
  norm_cast

/-- The derivative of xiLagarias satisfies the conjugation symmetry.

For a holomorphic f with f(conj s) = conj(f(s)), we have f'(conj s) = conj(f'(s)).
This can be seen by differentiating f(conj s) = conj(f(s)) along a real parameter. -/
lemma deriv_xiLagarias_conj (s : ℂ) :
    deriv xiLagarias (starRingEnd ℂ s) = starRingEnd ℂ (deriv xiLagarias s) := by
  -- Step 1: show `xiLagarias` is fixed by the involution `z ↦ conj (f (conj z))`.
  have hfun : (fun z : ℂ => conj (xiLagarias (conj z))) = xiLagarias := by
    funext z
    -- Rewrite `xiLagarias_conj` into a `conj`-statement.
    have hz' : xiLagarias (starRingEnd ℂ z) = starRingEnd ℂ (xiLagarias z) := xiLagarias_conj z
    have hzL : starRingEnd ℂ z = conj z := by
      calc
        starRingEnd ℂ z = star z := by simpa using (starRingEnd_apply (R := ℂ) z)
        _ = conj z := by rfl
    have hzR : starRingEnd ℂ (xiLagarias z) = conj (xiLagarias z) := by
      calc
        starRingEnd ℂ (xiLagarias z) = star (xiLagarias z) := by
          simpa using (starRingEnd_apply (R := ℂ) (xiLagarias z))
        _ = conj (xiLagarias z) := by rfl
    have hz : xiLagarias (conj z) = conj (xiLagarias z) := by
      -- Rewrite both sides of `hz'` using `hzL` and `hzR`.
      -- (`rw` works inside `xiLagarias (·)` since it's definitional rewriting of the argument.)
      simpa [hzL, hzR] using hz'
    -- Now conjugate both sides and simplify.
    calc
      conj (xiLagarias (conj z)) = conj (conj (xiLagarias z)) := by rw [hz]
      _ = xiLagarias z := by simp

  -- Step 2: differentiate `conj (xiLagarias (conj z)) = xiLagarias z` via `deriv_conj_conj`.
  have hder_base :
      deriv (fun z : ℂ => conj (xiLagarias (conj z))) (conj s) = conj (deriv xiLagarias s) := by
    simpa using (deriv_conj_conj (f := xiLagarias) (p := s))

  -- Replace the LHS derivative using `hfun`.
  have hder_eq :
      deriv (fun z : ℂ => conj (xiLagarias (conj z))) (conj s) = deriv xiLagarias (conj s) := by
    simpa using congrArg (fun g : ℂ → ℂ => deriv g (conj s)) hfun

  have hconj : deriv xiLagarias (conj s) = conj (deriv xiLagarias s) :=
    hder_eq.symm.trans hder_base

  -- Step 3: `conj` is notation for `starRingEnd`, so this is already exactly the goal.
  exact hconj

/-- The log-derivative of xiLagarias satisfies the conjugation symmetry.

From deriv ξ (conj s) = conj(deriv ξ s) and ξ(conj s) = conj(ξ s):
logDeriv ξ (conj s) = deriv ξ (conj s) / ξ(conj s)
                    = conj(deriv ξ s) / conj(ξ s)
                    = conj(deriv ξ s / ξ s)
                    = conj(logDeriv ξ s)
-/
lemma logDeriv_xiLagarias_conj (s : ℂ) :
    logDeriv xiLagarias (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv xiLagarias s) := by
  simp only [logDeriv, Pi.div_apply]
  rw [deriv_xiLagarias_conj, xiLagarias_conj]
  simp only [starRingEnd_apply, map_div₀]

/-- On the critical line, logDeriv xiLagarias is purely imaginary.

This follows from combining:
1. ξ(1-s) = ξ(s) → logDeriv ξ (1-s) = -logDeriv ξ (s)
2. ξ(conj s) = conj(ξ(s)) → logDeriv ξ (conj s) = conj(logDeriv ξ (s))
3. On critical line: 1-s = conj(s)

Combining: conj(logDeriv ξ s) = logDeriv ξ (conj s) = logDeriv ξ (1-s) = -logDeriv ξ s.
So logDeriv ξ s = -conj(logDeriv ξ s), which means Re(logDeriv ξ s) = 0. -/
lemma logDeriv_xiLagarias_purely_imaginary_on_critical_line (t : ℝ) :
    (logDeriv xiLagarias (1/2 + I * t)).re = 0 := by
  set s : ℂ := 1/2 + I * t
  -- On the critical line, conj(s) = 1 - s.
  have h_conj_s : starRingEnd ℂ s = 1 - s := by
    apply Complex.ext
    · simp [s]; norm_num
    · simp [s]
  -- From functional equation: logDeriv ξ (1-s) = -logDeriv ξ s
  have h1 : logDeriv xiLagarias (1 - s) = - logDeriv xiLagarias s := logDeriv_xiLagarias_one_sub s
  -- From conjugation: logDeriv ξ (conj s) = conj(logDeriv ξ s)
  have h2 : logDeriv xiLagarias (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv xiLagarias s) :=
    logDeriv_xiLagarias_conj s
  -- Combining on critical line: conj(logDeriv ξ s) = -logDeriv ξ s
  have h_anti : starRingEnd ℂ (logDeriv xiLagarias s) = - logDeriv xiLagarias s := by
    rw [← h2, h_conj_s, h1]
  -- conj(z) = -z means z = -conj(z).
  -- Let z = a + bi. Then conj(z) = a - bi = -(a + bi) = -a - bi.
  -- So a = -a and -b = -b. Hence a = 0.
  have h_re : (logDeriv xiLagarias s).re = 0 := by
    have heq := congr_arg Complex.re h_anti
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_re, Complex.neg_re] at heq
    -- heq : (logDeriv xiLagarias s).re = -(logDeriv xiLagarias s).re
    linarith
  exact h_re

/-- On the critical line, xiLagarias is real-valued. -/
lemma xiLagarias_real_on_critical_line (t : ℝ) : (xiLagarias (1/2 + I * t)).im = 0 := by
  set s : ℂ := 1/2 + I * t
  have h_conj_s : starRingEnd ℂ s = 1 - s := by
    apply Complex.ext
    · simp [s]; norm_num
    · simp [s]
  have h1 : xiLagarias (starRingEnd ℂ s) = starRingEnd ℂ (xiLagarias s) := xiLagarias_conj s
  have h2 : xiLagarias (starRingEnd ℂ s) = xiLagarias (1 - s) := by rw [h_conj_s]
  have h3 : xiLagarias (1 - s) = xiLagarias s := xiLagarias_one_sub s
  have h_real : starRingEnd ℂ (xiLagarias s) = xiLagarias s := by
    rw [← h1, h2, h3]
  -- starRingEnd ℂ z = z iff z.im = 0.
  simpa using (Complex.conj_eq_iff_im.mp h_real)

/-- The functional-equation log-derivative identity specialized to vertical-line points `c - it`. -/
lemma logDeriv_xiLagarias_leftEdge (c t : ℝ) :
    logDeriv xiLagarias (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv xiLagarias ((c : ℂ) + ((-t : ℝ) : ℂ) * I) := by
  -- Apply `logDeriv_xiLagarias_one_sub` to `s = c - it` and simplify `1 - (c - it)`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
    (logDeriv_xiLagarias_one_sub (s := (c : ℂ) + ((-t : ℝ) : ℂ) * I))

/-!
## Zeros: relating `xiLagarias` and `riemannZeta` (basic correspondence lemmas)

These lemmas are not the Route 3 bottleneck; they are routine “interface glue”
needed to connect Lagarias-style statements (formulated in terms of `ξ`) with
Mathlib's `RiemannHypothesis` predicate (formulated in terms of `ζ`).

We keep hypotheses explicit to avoid sweeping analytic subtleties under the rug.
-/

lemma completedRiemannZeta_eq_zero_of_riemannZeta_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hsre : 0 < s.re) (hz : riemannZeta s = 0) :
    completedRiemannZeta s = 0 := by
  have hΓ : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hdef := riemannZeta_def_of_ne_zero (s := s) hs0
  have hdiv : completedRiemannZeta s / Complex.Gammaℝ s = 0 := by
    simpa [hdef] using hz
  rcases (div_eq_zero_iff).1 hdiv with hcomp | hΓ0
  · exact hcomp
  · exact False.elim (hΓ hΓ0)

lemma xiLagarias_eq_zero_of_riemannZeta_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hsre : 0 < s.re) (hz : riemannZeta s = 0) :
    xiLagarias s = 0 := by
  have hcomp : completedRiemannZeta s = 0 :=
    completedRiemannZeta_eq_zero_of_riemannZeta_eq_zero (s := s) hs0 hsre hz
  unfold xiLagarias
  simp [hcomp]

lemma riemannZeta_eq_zero_of_xiLagarias_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsre : 0 < s.re) (hxi : xiLagarias s = 0) :
    riemannZeta s = 0 := by
  have hΓ : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hdef := riemannZeta_def_of_ne_zero (s := s) hs0
  have hpref : ((1/2 : ℂ) * s * (s - 1)) ≠ 0 := by
    have hhalf : (1/2 : ℂ) ≠ 0 := by norm_num
    have hsMinus1 : s - 1 ≠ 0 := by
      intro h
      apply hs1
      exact sub_eq_zero.mp h
    have h1 : (1/2 : ℂ) * s ≠ 0 := mul_ne_zero hhalf hs0
    have h2 : ((1/2 : ℂ) * s) * (s - 1) ≠ 0 := mul_ne_zero h1 hsMinus1
    simpa [mul_assoc] using h2
  -- Extract `completedRiemannZeta s = 0` from `xiLagarias s = 0`.
  have hcomp : completedRiemannZeta s = 0 := by
    unfold xiLagarias at hxi
    -- reassociate to isolate the `completedRiemannZeta` factor
    have hxi' : ((1/2 : ℂ) * s * (s - 1)) * completedRiemannZeta s = 0 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hxi
    rcases mul_eq_zero.mp hxi' with hpre0 | hcomp0
    · exact False.elim (hpref hpre0)
    · exact hcomp0
  -- Now use `ζ = Λ / Γ` (Mathlib's interface) and the nonvanishing of `Γ`.
  rw [hdef]
  simp [hcomp, hΓ]

/--
A packaged set of explicit-formula functionals in Lagarias' Mellin normalization.

`W0(f) = M[f](0)`, `W2(f) = M[f](1)`, and `W1(f) = ∑_ρ M[f](ρ)` (symmetric summation).
We keep `W1` and `Warith` abstract, since their analytic definition/convergence
is part of the Route 3 bottleneck.
-/
structure LagariasFramework (F : Type) [TestSpace F] where
  /-- The spectral zero-sum functional `W^{(1)}(f) = ∑_ρ M[f](ρ)` (symmetric summation). -/
  W1 : F → ℂ
  /-- The arithmetic-side functional `W_arith(f) = W_∞(f) + ∑_p W_p(f)`. -/
  Warith : F → ℂ

  /-- Lagarias Thm 3.1 (Explicit Formula): `W_spec(f) = W_arith(f)` for all nice `f`. -/
  explicitFormula : ∀ f : F, M[f](1) - W1 f + M[f](0) = Warith f

  /-- Lagarias Thm 3.2 (Weil positivity): `RH ↔ (∀f, Re(W1(f*~\bar f)) ≥ 0)`. -/
  weilPositivity :
      RiemannHypothesis ↔ (∀ f : F, 0 ≤ (W1 (TestSpace.quad (F:=F) f)).re)

/-- `W^{(2)}(f) = M[f](1)` (spectral boundary term). -/
def W2 {F : Type} [TestSpace F] (f : F) : ℂ := M[f](1)

/-- `W^{(0)}(f) = M[f](0)` (spectral boundary term). -/
def W0 {F : Type} [TestSpace F] (f : F) : ℂ := M[f](0)

/-- `W_spec(f) = W2(f) - W1(f) + W0(f)` (Lagarias). -/
def Wspec {F : Type} [TestSpace F] (f : F) (L : LagariasFramework F) : ℂ :=
  W2 f - L.W1 f + W0 f

-- Convenience projection: view `Wspec` as a function once `L` is fixed.
namespace LagariasFramework

variable {F : Type} [TestSpace F] (L : LagariasFramework F)

/-- `W_spec` as a unary functional for a fixed framework. -/
def Wspec (f : F) : ℂ :=
  (W2 f) - (L.W1 f) + (W0 f)

/-- `WeilGate`: the explicit-formula positivity hypothesis (the Route 3 bottleneck). -/
def WeilGate : Prop := ∀ f : F, 0 ≤ (L.W1 (TestSpace.quad (F:=F) f)).re

end LagariasFramework

-- Provide the `Wspec` used in the structure field above.
-- (We keep it outside the structure to avoid dependent recursion issues.)
@[simp] lemma Wspec_eq (F : Type) [TestSpace F] (L : LagariasFramework F) (f : F) :
    (LagariasFramework.Wspec (F:=F) L f) = W2 f - L.W1 f + W0 f := rfl

end ExplicitFormula
end RiemannRecognitionGeometry
