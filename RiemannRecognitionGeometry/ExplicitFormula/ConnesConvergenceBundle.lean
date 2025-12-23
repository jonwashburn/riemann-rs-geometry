/-
# Route 3′ (Connes): “missing steps” convergence bundle (typed surface)

This file turns the informal Section 7–8 “Outlook / missing steps” of
Connes–Consani–Moscovici (`arXiv:2511.22755`) into a Lean-facing hypothesis bundle.

What the paper makes explicit is:

- **(M1)** a *simple-even* gate for the smallest eigenvector of the Weil quadratic form `Q_{W,λ}`,
- **(M2)** a quantitative approximation statement `k_λ ≈ ξ_λ` strong enough to pass to limits of
  (regularized-determinant / Fourier-transform) entire functions,
- plus the “soft” analytic step: uniform-on-substrips convergence implies RH via Hurwitz.

We already package the “soft” Hurwitz step in `HurwitzGate.lean` and the top-level RH target in
`ConnesHurwitzBridge.lean`. Here we isolate the remaining analytic content as named fields, so
future work can focus exactly on them.
-/

import RiemannRecognitionGeometry.ExplicitFormula.ConnesHurwitzBridge
import RiemannRecognitionGeometry.ExplicitFormula.RealZeros
import RiemannRecognitionGeometry.ExplicitFormula.ConnesSection7
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Topology.ContinuousOn

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex Filter Set

/-! ## A tiny “nontriviality” surface

`HurwitzGate.lean` requires a witness that the limit function is not identically zero on each
connected component where we apply Hurwitz.

For `Ξ` this is completely harmless (classically `Ξ(0) ≠ 0`, and `Ξ` is entire), but we keep it
as explicit axioms to avoid pulling in extra special-value theory.
-/

namespace ConnesConvergenceBundle

open scoped Topology

/-!
## Discharging the “nontriviality” witness for `Ξ`

`HurwitzGate.lean` asks for a witness `∃ z ∈ U, f z ≠ 0` on each open, preconnected region `U`
where Hurwitz is applied. For `Ξ`, this is classical and does *not* depend on RH:

- we can compute one explicit value `Ξ(-(3/2)·i) = ξ(2) ≠ 0` (Euler-product half-plane),
- if `Ξ` vanished on an open set inside the strip, the identity theorem would force `Ξ ≡ 0` on a
  connected domain, contradicting the explicit nonzero value.

We keep the proof entirely inside “soft” complex analysis + `ξ(2) ≠ 0`.
-/

private lemma differentiableAt_xiLagarias_of_ne0_ne1 {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ xiLagarias s := by
  -- Same argument as `ZetaInstantiation.differentiableAt_xiLagarias_of_ne0_ne1`, but kept local
  -- to avoid importing the full ζ instantiation stack.
  have hΛ : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta (s := s) hs0 hs1
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z) s :=
    (differentiableAt_id.const_mul (1 / 2 : ℂ))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => z - (1 : ℂ)) s :=
    (differentiableAt_id.sub_const (1 : ℂ))
  have h23 : DifferentiableAt ℂ (fun z : ℂ => (z - (1 : ℂ)) * completedRiemannZeta z) s :=
    h2.mul hΛ
  have h :
      DifferentiableAt ℂ
        (fun z : ℂ => ((1 / 2 : ℂ) * z) * ((z - (1 : ℂ)) * completedRiemannZeta z)) s :=
    h1.mul h23
  have hxi :
      xiLagarias =
        (fun z : ℂ => ((1 / 2 : ℂ) * z) * ((z - (1 : ℂ)) * completedRiemannZeta z)) := by
    funext z
    unfold xiLagarias
    simp [mul_assoc]
  simpa [hxi] using h

private lemma riemannXi_ne_zero_at_neg_three_halves_I : riemannXi (-(3 / 2 : ℝ) * Complex.I) ≠ 0 := by
  -- Compute: `1/2 + I * (-(3/2)I) = 2`, hence `Ξ(-(3/2)i) = ξ(2) ≠ 0`.
  have hcalc : (1 / 2 : ℂ) + Complex.I * (-(3 / 2 : ℝ) * Complex.I) = (2 : ℂ) := by
    -- `I * (r * I) = r * (I^2) = -r`
    ring_nf
    -- `I^2 = -1`
    simp [Complex.I_sq]
    norm_num
  have h2 : xiLagarias (2 : ℂ) ≠ 0 :=
    xiLagarias_ne_zero_of_re_gt_one (s := (2 : ℂ)) (by norm_num)
  -- Avoid fragile syntactic matching under simp by rewriting through `congrArg`.
  have hx : riemannXi (-(3 / 2 : ℝ) * Complex.I) = xiLagarias (2 : ℂ) := by
    simpa [riemannXi] using congrArg xiLagarias hcalc
  -- Rewrite the goal using `hx` and finish with `h2`.
  -- `rw` rewrites the goal (not the hypothesis), so we avoid simp-orientation issues.
  -- After rewriting, the goal becomes `xiLagarias (2 : ℂ) ≠ 0`.
  -- (Use `rw` directly rather than `simpa using` to avoid simp rewriting the wrong side.)
  rw [hx]
  exact h2

private lemma differentiableOn_riemannXi_on_punctured : DifferentiableOn ℂ riemannXi ({Complex.I / 2, (-Complex.I) / 2}ᶜ) := by
  intro t ht
  have ht' : t ≠ Complex.I / 2 ∧ t ≠ (-Complex.I) / 2 := by
    simpa using ht
  have hs0 : (1 / 2 : ℂ) + Complex.I * t ≠ 0 := by
    intro hs
    -- Solve `1/2 + I*t = 0` ⇒ `t = I/2` by multiplying both sides by `I`.
    have hsI : Complex.I * ((1 / 2 : ℂ) + Complex.I * t) = 0 := by
      simpa [hs] using congrArg (fun z : ℂ => Complex.I * z) hs
    have hsI' : (Complex.I / 2 : ℂ) - t = 0 := by
      -- Expand and use `I*(I*t) = (I*I)*t = -t`.
      simpa [mul_add, mul_assoc, (mul_assoc Complex.I Complex.I t).symm,
        Complex.I_mul_I, sub_eq_add_neg, div_eq_mul_inv] using hsI
    have htEq : t = Complex.I / 2 := by
      exact (sub_eq_zero.mp hsI').symm
    exact ht'.1 htEq
  have hs1 : (1 / 2 : ℂ) + Complex.I * t ≠ 1 := by
    intro hs
    -- Solve `1/2 + I*t = 1` ⇒ `I*t = 1/2` ⇒ `t = -I/2`.
    have hIt : Complex.I * t = (1 / 2 : ℂ) := by
      -- Subtract `1/2` from both sides: `(1/2 + I*t) - 1/2 = 1 - 1/2`.
      have h := congrArg (fun z : ℂ => z - (1 / 2 : ℂ)) hs
      -- Simplify the LHS to `I*t` and the RHS to `1/2`.
      -- `1 - 1/2` is definitionally `1 + (-1/2)`; `norm_num` closes the arithmetic.
      have : (Complex.I * t) = (1 : ℂ) - (1 / 2 : ℂ) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
      -- Now `1 - 1/2 = 1/2`.
      simpa [sub_eq_add_neg] using (this.trans (by norm_num))
    have htEq : t = (-Complex.I) / 2 := by
      -- Multiply by `(-I)` and simplify `(-I)*(I*t) = t`.
      have h := congrArg (fun z : ℂ => (-Complex.I) * z) hIt
      -- Reassociate `(-I)*(I*t)` and use `I*I = -1`.
      simpa [mul_assoc, (mul_assoc (-Complex.I) Complex.I t).symm,
        Complex.I_mul_I, div_eq_mul_inv] using h
    exact ht'.2 htEq
  have hlin : DifferentiableAt ℂ (fun u : ℂ => (1 / 2 : ℂ) + Complex.I * u) t := by
    have hmul : DifferentiableAt ℂ (fun u : ℂ => Complex.I * u) t :=
      (differentiableAt_id.const_mul Complex.I)
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) t := by
      simpa using (differentiableAt_const (c := (1 / 2 : ℂ)) (x := t))
    simpa using hconst.add hmul
  have hxi : DifferentiableAt ℂ xiLagarias ((1 / 2 : ℂ) + Complex.I * t) :=
    differentiableAt_xiLagarias_of_ne0_ne1 (s := (1 / 2 : ℂ) + Complex.I * t) hs0 hs1
  -- compose
  exact (hxi.comp t hlin).differentiableWithinAt

private lemma isPreconnected_punctured_two_points :
    IsPreconnected ({Complex.I / 2, (-Complex.I) / 2}ᶜ : Set ℂ) := by
  -- Use the general “complement of a countable set is connected in rank > 1” lemma over `ℝ`,
  -- specialized to `ℂ` (rank 2 over `ℝ`).
  have hrank : 1 < Module.rank ℝ ℂ := by
    simpa [Complex.rank_real_complex] using (Nat.one_lt_ofNat : 1 < (2 : Nat))
  have hcount : ({Complex.I / 2, (-Complex.I) / 2} : Set ℂ).Countable := by
    simpa using (Set.finite_insert _ (Set.finite_singleton _)).countable
  exact (Set.Countable.isConnected_compl_of_one_lt_rank (E := ℂ) hrank hcount).isPreconnected

private lemma isOpen_punctured_two_points :
    IsOpen ({Complex.I / 2, (-Complex.I) / 2}ᶜ : Set ℂ) := by
  -- Finite sets are closed in a `T1Space`, so their complements are open.
  have hfinite : ({Complex.I / 2, (-Complex.I) / 2} : Set ℂ).Finite := by
    simpa using (Set.finite_singleton ((-Complex.I) / 2)).insert (Complex.I / 2)
  have hclosed : IsClosed ({Complex.I / 2, (-Complex.I) / 2} : Set ℂ) :=
    hfinite.isClosed
  simpa using hclosed.isOpen_compl

private lemma analyticOnNhd_riemannXi_on_punctured :
    AnalyticOnNhd ℂ riemannXi ({Complex.I / 2, (-Complex.I) / 2}ᶜ : Set ℂ) := by
  exact DifferentiableOn.analyticOnNhd
    (differentiableOn_riemannXi_on_punctured)
    (isOpen_punctured_two_points)

theorem riemannXi_nontriv_upper : ∃ z ∈ upperStrip, riemannXi z ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ z : ℂ, z ∈ upperStrip → riemannXi z = 0 := by
    intro z hzU
    by_contra hne
    exact h ⟨z, hzU, hne⟩
  -- Work on the connected open domain `ℂ \ {± i/2}` where `Ξ` is analytic.
  let U : Set ℂ := ({Complex.I / 2, (-Complex.I) / 2}ᶜ : Set ℂ)
  have hAnalytic : AnalyticOnNhd ℂ riemannXi U := analyticOnNhd_riemannXi_on_punctured
  have hUconn : IsPreconnected U := isPreconnected_punctured_two_points
  -- Pick a point in the upper strip.
  let z0 : ℂ := (1 / 4 : ℝ) * Complex.I
  have hz0U : z0 ∈ U := by
    -- `Im(z0)=1/4`, so `z0 ≠ ± i/2`.
    have hz0neI : z0 ≠ Complex.I / 2 := by
      intro hEq
      have him := congrArg Complex.im hEq
      have : (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
        simpa [z0] using him
      norm_num at this
    have hz0neNegI : z0 ≠ (-Complex.I) / 2 := by
      intro hEq
      have him := congrArg Complex.im hEq
      have : (1 / 4 : ℝ) = (-1 / 2 : ℝ) := by
        simpa [z0] using him
      norm_num at this
    -- membership in the complement of `{a,b}` is `z ≠ a ∧ z ≠ b`
    simpa [U] using And.intro hz0neI hz0neNegI
  have hz0Upper : z0 ∈ upperStrip := by
    -- `0 < Im(z0) = 1/4 < 1/2`.
    have hz0im : z0.im = (1 / 4 : ℝ) := by simp [z0]
    constructor
    · -- 0 < 1/4
      have : (0 : ℝ) < (1 / 4 : ℝ) := by norm_num
      simpa [hz0im] using this
    · -- 1/4 < 1/2
      have : (1 / 4 : ℝ) < (1 / 2 : ℝ) := by norm_num
      simpa [hz0im] using this
  -- From `Ξ = 0` on an open neighborhood (upper strip), we get frequent zeros near `z0`.
  have hnhds : upperStrip ∈ 𝓝 z0 := isOpen_upperStrip.mem_nhds hz0Upper
  have hmem : ({z0}ᶜ ∩ upperStrip) ∈ 𝓝[({z0}ᶜ)] z0 := inter_mem_nhdsWithin ({z0}ᶜ) hnhds
  have hEv : ∀ᶠ z in 𝓝[≠] z0, riemannXi z = 0 := by
    -- `𝓝[≠] z0 = 𝓝[{z0}ᶜ] z0`.
    have : (∀ᶠ z in 𝓝[{z0}ᶜ] z0, riemannXi z = 0) := by
      refine Filter.mem_of_superset hmem ?_
      intro z hz'
      exact hz z hz'.2
    simpa using this
  have hEqOn : EqOn riemannXi 0 U :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero (𝕜 := ℂ)
      (f := riemannXi) (U := U) (z₀ := z0) hAnalytic hUconn hz0U hEv.frequently
  -- Contradiction: `Ξ(-(3/2)i) = ξ(2) ≠ 0`.
  have htU : (-(3 / 2 : ℝ) * Complex.I) ∈ U := by
    -- imaginary part is `-3/2`, so it is not `±1/2`.
    have htneI : (-(3 / 2 : ℝ) * Complex.I) ≠ Complex.I / 2 := by
      intro hEq
      have := congrArg Complex.im hEq
      norm_num at this
    have htneNegI : (-(3 / 2 : ℝ) * Complex.I) ≠ (-Complex.I) / 2 := by
      intro hEq
      have := congrArg Complex.im hEq
      norm_num at this
    simpa [U] using And.intro htneI htneNegI
  have : riemannXi (-(3 / 2 : ℝ) * Complex.I) = 0 := hEqOn htU
  exact riemannXi_ne_zero_at_neg_three_halves_I (by simpa using this)

theorem riemannXi_nontriv_lower : ∃ z ∈ lowerStrip, riemannXi z ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ z : ℂ, z ∈ lowerStrip → riemannXi z = 0 := by
    intro z hzL
    by_contra hne
    exact h ⟨z, hzL, hne⟩
  -- Same proof as `riemannXi_nontriv_upper`, but with a point in the lower strip.
  let U : Set ℂ := ({Complex.I / 2, (-Complex.I) / 2}ᶜ : Set ℂ)
  have hAnalytic : AnalyticOnNhd ℂ riemannXi U := analyticOnNhd_riemannXi_on_punctured
  have hUconn : IsPreconnected U := isPreconnected_punctured_two_points
  let z0 : ℂ := (-(1 / 4 : ℝ)) * Complex.I
  have hz0U : z0 ∈ U := by
    have hz0neI : z0 ≠ Complex.I / 2 := by
      intro hEq
      have him := congrArg Complex.im hEq
      have : (-(1 / 4 : ℝ)) = (1 / 2 : ℝ) := by
        simpa [z0] using him
      norm_num at this
    have hz0neNegI : z0 ≠ (-Complex.I) / 2 := by
      intro hEq
      have him := congrArg Complex.im hEq
      have : (-(1 / 4 : ℝ)) = (-1 / 2 : ℝ) := by
        simpa [z0] using him
      norm_num at this
    simpa [U] using And.intro hz0neI hz0neNegI
  have hz0Lower : z0 ∈ lowerStrip := by
    have hz0im : z0.im = (-(1 / 4 : ℝ)) := by simp [z0]
    constructor
    · -- -1/2 < -1/4
      have : (- (1 / 2 : ℝ)) < (-(1 / 4 : ℝ)) := by norm_num
      simpa [hz0im] using this
    · -- -1/4 < 0
      have : (-(1 / 4 : ℝ)) < (0 : ℝ) := by norm_num
      simpa [hz0im] using this
  have hnhds : lowerStrip ∈ 𝓝 z0 := isOpen_lowerStrip.mem_nhds hz0Lower
  have hmem : ({z0}ᶜ ∩ lowerStrip) ∈ 𝓝[({z0}ᶜ)] z0 := inter_mem_nhdsWithin ({z0}ᶜ) hnhds
  have hEv : ∀ᶠ z in 𝓝[≠] z0, riemannXi z = 0 := by
    have : (∀ᶠ z in 𝓝[{z0}ᶜ] z0, riemannXi z = 0) := by
      refine Filter.mem_of_superset hmem ?_
      intro z hz'
      exact hz z hz'.2
    simpa using this
  have hEqOn : EqOn riemannXi 0 U :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero (𝕜 := ℂ)
      (f := riemannXi) (U := U) (z₀ := z0) hAnalytic hUconn hz0U hEv.frequently
  have htU : (-(3 / 2 : ℝ) * Complex.I) ∈ U := by
    have htneI : (-(3 / 2 : ℝ) * Complex.I) ≠ Complex.I / 2 := by
      intro hEq
      have := congrArg Complex.im hEq
      norm_num at this
    have htneNegI : (-(3 / 2 : ℝ) * Complex.I) ≠ (-Complex.I) / 2 := by
      intro hEq
      have := congrArg Complex.im hEq
      norm_num at this
    simpa [U] using And.intro htneI htneNegI
  have : riemannXi (-(3 / 2 : ℝ) * Complex.I) = 0 := hEqOn htU
  exact riemannXi_ne_zero_at_neg_three_halves_I (by simpa using this)

end ConnesConvergenceBundle

/--
Abstract placeholder for the Connes–Consani–Moscovici approximant entire functions.

In the paper these are (normalized) regularized determinants / Fourier transforms of the ground
state eigenfunction for a truncated Weil form, indexed by parameters `(λ,N)` and then sent to
infinity in a suitable regime.

We do *not* implement the operator construction here; we only state what properties we would
need to feed the Hurwitz gate.
-/
structure ConnesApproximants where
  F : ℕ → ℂ → ℂ
  /-- Holomorphy on the strip `|Im| < 1/2` (stronger than needed, but convenient). -/
  holo_on_strip : ∀ n, DifferentiableOn ℂ (F n) strip
  /-- All zeros are real (stronger than needed; implies `ZeroFreeOn` on upper/lower strip). -/
  allZerosReal : ∀ n, AllZerosReal (F n)

/-
## Section 8 “missing steps” (typed surfaces)

The CCM paper phrases the remaining work in terms of:
- a “simple-even” property for the *ground state* of the semilocal Weil quadratic form `Q_{W,λ}`,
- and a quantitative approximation statement `k_λ ≈ ξ_λ` (up to scalar) strong enough to transfer
  convergence of transforms / zeros.

We do not implement `Q_{W,λ}` or the map `E`/prolate-wave operator here; instead we expose *Lean-facing
targets* that record the **exact shape** of what Section 8 asks for.
-/

/-- Placeholder predicate: `IsWeilGroundState λ ξ` means “`ξ = ξ_λ` is the normalized ground-state eigenfunction
of the semilocal Weil quadratic form `Q_{W,λ}`” (Section 8 of `arXiv:2511.22755`). -/
opaque IsWeilGroundState (lam : ℝ) (ξ : ℝ → ℂ) : Prop

/-- **M1 (Section 8):** the semilocal Weil ground state exists, is even (under `u ↦ u⁻¹`), and is unique up to scalar
(simplicity of the smallest eigenvalue). -/
structure ConnesMissingStepSimpleEven where
  /-- The family `λ ↦ ξ_λ`. -/
  ξ : ℝ → (ℝ → ℂ)
  /-- Ground-state condition (unimplemented; kept as an explicit predicate). -/
  ground : ∀ᶠ lam : ℝ in atTop, IsWeilGroundState lam (ξ lam)
  /-- Evenness gate (paper wording: invariance under `u ↦ u^{-1}` on `[λ⁻¹,λ]`). -/
  even : ∀ᶠ lam : ℝ in atTop, ∀ u : ℝ, (ξ lam) u⁻¹ = (ξ lam) u
  /-- Normalization used in the paper: `ξ_λ(λ) = 1`. -/
  normalized : ∀ᶠ lam : ℝ in atTop, (ξ lam) lam = 1
  /-- Simplicity/uniqueness: any other ground state is a scalar multiple of `ξ_λ`. -/
  simple :
    ∀ᶠ lam : ℝ in atTop,
      ∀ ψ : ℝ → ℂ, IsWeilGroundState lam ψ → ∃ c : ℂ, ψ = c • ξ lam

/-- **M2 (Section 8):** the “educated guess” `k_λ` approximates (a scalar multiple of) the true ground state `ξ_λ`
uniformly on the semilocal interval `[λ⁻¹,λ]` with an error bound tending to `0`. -/
structure ConnesMissingStep_kLam_approximates_xiLam (ξ : ℝ → (ℝ → ℂ)) where
  /-- The family `λ ↦ k_λ` (paper: `k_λ := E(h_λ)`). -/
  k : ℝ → (ℝ → ℂ)
  /-- Scalar renormalization `c_λ` (paper: “up to a multiplicative scalar”). -/
  c : ℝ → ℂ
  /-- Uniform error bound on `[λ⁻¹,λ]`. -/
  ε : ℝ → ℝ
  /-- Uniform-on-interval control (sup-norm style) for large `λ`. -/
  bound :
    ∀ᶠ lam : ℝ in atTop,
      ∀ u : ℝ,
        u ∈ Set.Icc (lam⁻¹) lam → Complex.abs (k lam u - (c lam) * (ξ lam u)) ≤ ε lam
  /-- Error bound tends to `0` as `λ → ∞`. -/
  ε_tendsto0 : Tendsto ε atTop (nhds 0)

/--
Connes Route‑3′ convergence bundle (what Section 8 calls “the missing steps”).

This is intentionally a *thin* API:
- `approximants` packages “zeros are real” (self-adjointness) + holomorphy on the strip.
- `tendstoXi` is the locally-uniform convergence that, together with `approximants`, yields the
  Hurwitz gate.

The two named booleans `simpleEven_gate` and `kλ_approximates_groundState` are placeholders for
the genuinely hard analytic content that CCM identify (and which is not proved in the paper).
-/
structure ConnesConvergenceBundle where
  approximants : ConnesApproximants
  /-- Locally-uniform convergence on the strip `|Im| < 1/2` to Riemann `Ξ`. -/
  tendstoXi : TendstoLocallyUniformlyOn approximants.F riemannXi atTop strip

  /-- **M1 (Section 8):** “simple-even” gate for the semilocal Weil ground state. -/
  missing_simpleEven_QWlam : ConnesMissingStepSimpleEven
  /-- **M2 (Section 8):** `k_λ ≈ ξ_λ` (up to scalar) as a uniform-on-interval approximation with vanishing error. -/
  missing_kLam_approximates_xiLam :
    ConnesMissingStep_kLam_approximates_xiLam missing_simpleEven_QWlam.ξ

namespace ConnesConvergenceBundle

variable (C : ConnesConvergenceBundle)

/-!
## From the bundle to the already-typed Hurwitz gate

Once `tendstoXi` is established (the main analytic work), we can pass immediately to
`ConnesHurwitzAssumptions` and thus to the RH target.
-/

def toHurwitzGate : HurwitzOffRealAxisInStripGate (f := riemannXi) where
  F := C.approximants.F
  holo_upper := by
    intro n
    -- Restrict holomorphy-on-strip to `upperStrip` using subset relation.
    intro z hz
    -- `DifferentiableWithinAt` is monotone in the set argument.
    exact (C.approximants.holo_on_strip n z (upperStrip_subset_strip hz)).mono upperStrip_subset_strip
  holo_lower := by
    intro n
    intro z hz
    exact (C.approximants.holo_on_strip n z (lowerStrip_subset_strip hz)).mono lowerStrip_subset_strip
  tendsto_strip := by
    -- Monotonicity: convergence on `strip` implies convergence on `strip` (identity).
    simpa using C.tendstoXi
  zeroFree_upper := fun n => zeroFreeOn_upperStrip_of_allZerosReal (C.approximants.allZerosReal n)
  zeroFree_lower := fun n => zeroFreeOn_lowerStrip_of_allZerosReal (C.approximants.allZerosReal n)
  nontriv_upper := riemannXi_nontriv_upper
  nontriv_lower := riemannXi_nontriv_lower

def toConnesHurwitzAssumptions : ConnesHurwitzAssumptions :=
  ⟨ConnesConvergenceBundle.toHurwitzGate C⟩

theorem riemannHypothesis_of_bundle (C : ConnesConvergenceBundle) : RiemannHypothesis :=
  riemannHypothesis_of_connesHurwitz (A := ConnesConvergenceBundle.toConnesHurwitzAssumptions C)

/-!
## Play A: a bridge lemma scaffold for `tendstoXi`

The Route‑3′ CCM story has a natural **two-stage** approximation:

- a “finite-rank” approximant (depending on `N`) is close to a “λ-level” object,
- and the λ-level object converges to `riemannXi` as `λ → ∞`.

On the Lean side, the *hard analysis* is in producing quantitative bounds; but the **gluing step**
from “uniform closeness on compacts” + “locally uniform convergence on the strip” to
`TendstoLocallyUniformlyOn` is purely topological. We isolate that gluing here.
-/

section TendstoBridge

open Topology Uniformity Filter Set

variable {α : Type*} {β : Type*} {ι : Type*} [TopologicalSpace α] [UniformSpace β]

/-- `TendstoUniformlyCloseOn F G p s` means: for every entourage `u`, eventually in `p`,
`F n` is `u`-close to the *varying* target `G n` uniformly on `s`.

This is the right notion when the “intermediate approximant” depends on the same index `n`
(e.g. `G n = F_{λ_n}` in a diagonal regime). -/
def TendstoUniformlyCloseOn (F G : ι → α → β) (p : Filter ι) (s : Set α) : Prop :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x : α, x ∈ s → (G n x, F n x) ∈ u

theorem tendstoUniformlyOn_of_tendstoUniformlyCloseOn
    {F G : ι → α → β} {f : α → β} {p : Filter ι} {s : Set α}
    (hclose : TendstoUniformlyCloseOn F G p s) (hG : TendstoUniformlyOn G f p s) :
    TendstoUniformlyOn F f p s := by
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, _htsymm, htcomp⟩
  filter_upwards [hG t ht, hclose t ht] with n hnG hnclose x hx
  have : (f x, F n x) ∈ t ○ t :=
    mem_compRel.2 ⟨G n x, hnG x hx, hnclose x hx⟩
  exact htcomp this

theorem tendstoLocallyUniformlyOn_of_forall_isCompact_tendstoUniformlyCloseOn
    {F G : ι → α → β} {f : α → β} {p : Filter ι} {s : Set α} [LocallyCompactSpace α]
    (hs : IsOpen s)
    (hclose : ∀ K : Set α, K ⊆ s → IsCompact K → TendstoUniformlyCloseOn F G p K)
    (hG : TendstoLocallyUniformlyOn G f p s) :
    TendstoLocallyUniformlyOn F f p s := by
  -- Reduce to compact subsets of `s`.
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hKs hK
  have hG_K : TendstoUniformlyOn G f p K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hs).1 hG K hKs hK
  exact tendstoUniformlyOn_of_tendstoUniformlyCloseOn (hclose K hKs hK) hG_K

end TendstoBridge

end ConnesConvergenceBundle

end ExplicitFormula
end RiemannRecognitionGeometry
