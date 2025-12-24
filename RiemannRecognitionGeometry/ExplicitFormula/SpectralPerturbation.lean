/-
# Spectral perturbation helper lemmas (finite-dimensional / Hilbert-space level)

This file is a **CCM Route‑3′ utility**: it does *not* build the Weil operator, but provides
general-purpose perturbation lemmas of the form

> (ground-state gap) + (operator-norm perturbation) ⇒ (ground-state vector is stable).

These are the classical “Davis–Kahan / min–max” style steps needed to attack CCM **M2**
(`ConnesMissingStep_kLam_approximates_xiLam`) once the analytic estimates
`δ(λ)` (perturbation size) and `g(λ)` (spectral gap) are supplied.
-/

import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Data.Complex.Abs

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open scoped Real InnerProductSpace
open Module.End

namespace SpectralPerturbation

/-! ## Basic operator-norm → quadratic-form bounds -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma abs_inner_clm_le_opNorm_mul_norm (T : H →L[ℂ] H) (x y : H) :
    Complex.abs ⟪T x, y⟫_ℂ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  -- `‖⟪T x, y⟫‖ ≤ ‖T x‖‖y‖ ≤ ‖T‖‖x‖‖y‖`
  have h1 : ‖⟪T x, y⟫_ℂ‖ ≤ ‖T x‖ * ‖y‖ := by
    simpa using (norm_inner_le_norm (𝕜 := ℂ) (T x) y)
  have h2 : ‖T x‖ ≤ ‖T‖ * ‖x‖ := by
    simpa using (T.le_opNorm x)
  -- turn `Complex.abs` into `‖·‖`
  simpa [Complex.abs, mul_assoc, mul_left_comm, mul_comm] using
    (le_trans h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg y)))

lemma abs_inner_clm_self_le_opNorm_mul_norm_sq (T : H →L[ℂ] H) (x : H) :
    Complex.abs ⟪T x, x⟫_ℂ ≤ ‖T‖ * ‖x‖ ^ 2 := by
  -- specialize the previous lemma with `y=x`
  have := abs_inner_clm_le_opNorm_mul_norm (T := T) (x := x) (y := x)
  -- rewrite `‖x‖*‖x‖` as `‖x‖^2`
  simpa [pow_two, mul_assoc] using this

lemma re_inner_clm_self_le_opNorm_mul_norm_sq (T : H →L[ℂ] H) (x : H) :
    Complex.re ⟪T x, x⟫_ℂ ≤ ‖T‖ * ‖x‖ ^ 2 := by
  have habs : Complex.abs ⟪T x, x⟫_ℂ ≤ ‖T‖ * ‖x‖ ^ 2 :=
    abs_inner_clm_self_le_opNorm_mul_norm_sq (T := T) x
  exact le_trans (Complex.re_le_abs _) habs

/-! ## A simple ground-state stability lemma (Rayleigh quotient + gap) -/

/--
`GroundGap A u λ g` means:
- `u` is a unit eigenvector of the self-adjoint operator `A` with eigenvalue `λ`,
- and `A` has a **quadratic-form gap** `g` on the orthogonal complement of `u`.

This is the minimal “typed surface” you need to run a Davis–Kahan style argument without invoking
the full spectral theorem.
-/
structure GroundGap (A : H →L[ℂ] H) (u : H) (lam g : ℝ) : Prop where
  selfAdjoint : IsSelfAdjoint A
  norm_u : ‖u‖ = 1
  eigen : A u = (lam : ℂ) • u
  gap_pos : 0 < g
  gap :
    ∀ w : H, ⟪u, w⟫_ℂ = 0 →
      Complex.re ⟪A w, w⟫_ℂ ≥ (lam + g) * ‖w‖ ^ 2

/--
**Ground-state stability (one-shot).**

Let `A` have a simple ground mode `u` with quadratic-form gap `g` on `u ⟂`.
If `B` is a perturbation with `‖B-A‖ ≤ δ` and `v` is a unit vector whose Rayleigh quotient for `B`
is no larger than that of `u` (e.g. `v` is a `B` ground state), then the component of `v`
orthogonal to `u` is small:
\[
  \|v - \langle u,v\rangle u\|^2 \le 2\delta/g.
\]

This is the cleanest “δ/g” inequality we can use downstream (with an embedding step to get sup norms).
-/
theorem groundGap_orthogonal_component_sq_le
    {A B : H →L[ℂ] H} {u v : H} {lam g δ : ℝ}
    (hGap : GroundGap (A := A) (u := u) (lam := lam) (g := g))
    (hBself : IsSelfAdjoint B)
    (hδ : ‖B - A‖ ≤ δ)
    (huv : Complex.re ⟪B v, v⟫_ℂ ≤ Complex.re ⟪B u, u⟫_ℂ)
    (hnormu : ‖u‖ = 1 := hGap.norm_u)
    (hnormv : ‖v‖ = 1) :
    ‖v - (⟪u, v⟫_ℂ) • u‖ ^ 2 ≤ (2 * δ) / g := by
  -- Set `w = v - ⟪u,v⟫ u` so `w ⟂ u`.
  let w : H := v - (⟪u, v⟫_ℂ) • u
  have huw : ⟪u, w⟫_ℂ = 0 := by
    -- Direct computation with `‖u‖ = 1`.
    have huu : ⟪u, u⟫_ℂ = (1 : ℂ) := by
      -- `⟪u,u⟫ = ‖u‖^2`
      simpa [inner_self_eq_norm_sq_to_K, hnormu] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u)
    -- `⟪u, v - ⟪u,v⟫u⟫ = ⟪u,v⟫ - ⟪u,v⟫⟪u,u⟫ = 0`.
    simp [w, inner_sub_right, inner_smul_right, huu]
  -- Rayleigh quotient sandwich:
  -- 1) `re ⟪B u,u⟫ ≤ re ⟪A u,u⟫ + δ`
  have hBu_le : Complex.re ⟪B u, u⟫_ℂ ≤ Complex.re ⟪A u, u⟫_ℂ + δ := by
    have :
        Complex.re ⟪(B - A) u, u⟫_ℂ ≤ ‖B - A‖ * ‖u‖ ^ 2 :=
      le_trans (re_inner_clm_self_le_opNorm_mul_norm_sq (T := (B - A)) u) (by
        exact le_of_eq rfl)
    have hBA : ‖B - A‖ * ‖u‖ ^ 2 ≤ δ * ‖u‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hδ (sq_nonneg ‖u‖)
    have h1 : Complex.re ⟪B u, u⟫_ℂ = Complex.re ⟪A u, u⟫_ℂ + Complex.re ⟪(B - A) u, u⟫_ℂ := by
      -- `B = A + (B-A)`
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, inner_add_left, inner_add_right]
    -- finish
    have h2 : Complex.re ⟪(B - A) u, u⟫_ℂ ≤ δ := by
      -- use unit norm of u
      have hu2 : ‖u‖ ^ 2 = (1 : ℝ) := by simpa [hnormu] using (one_pow (2 : Nat))
      -- bound by `‖B-A‖‖u‖^2 ≤ δ`
      have : Complex.re ⟪(B - A) u, u⟫_ℂ ≤ ‖B - A‖ * ‖u‖ ^ 2 :=
        re_inner_clm_self_le_opNorm_mul_norm_sq (T := (B - A)) u
      have : Complex.re ⟪(B - A) u, u⟫_ℂ ≤ δ * ‖u‖ ^ 2 :=
        le_trans this (mul_le_mul_of_nonneg_right hδ (sq_nonneg ‖u‖))
      simpa [hnormu, pow_two] using this
    -- combine
    linarith [h2]
  -- 2) `re ⟪B v,v⟫ ≥ re ⟪A v,v⟫ - δ`
  have hBv_ge : Complex.re ⟪B v, v⟫_ℂ ≥ Complex.re ⟪A v, v⟫_ℂ - δ := by
    -- `re ⟪Bv,v⟫ = re ⟪Av,v⟫ + re ⟪(B-A)v,v⟫`, and the last term is ≥ -δ
    have hEq : Complex.re ⟪B v, v⟫_ℂ = Complex.re ⟪A v, v⟫_ℂ + Complex.re ⟪(B - A) v, v⟫_ℂ := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, inner_add_left, inner_add_right]
    have hAbs : Complex.abs ⟪(B - A) v, v⟫_ℂ ≤ δ := by
      -- `|⟪(B-A)v,v⟫| ≤ ‖B-A‖‖v‖^2 ≤ δ`
      have : Complex.abs ⟪(B - A) v, v⟫_ℂ ≤ ‖B - A‖ * ‖v‖ ^ 2 :=
        abs_inner_clm_self_le_opNorm_mul_norm_sq (T := (B - A)) v
      have : Complex.abs ⟪(B - A) v, v⟫_ℂ ≤ δ * ‖v‖ ^ 2 :=
        le_trans this (mul_le_mul_of_nonneg_right hδ (sq_nonneg ‖v‖))
      simpa [hnormv, pow_two] using this
    have hRe_ge : Complex.re ⟪(B - A) v, v⟫_ℂ ≥ -δ := by
      have : Complex.re ⟪(B - A) v, v⟫_ℂ ≥ -δ := by
        have : Complex.abs ⟪(B - A) v, v⟫_ℂ ≤ δ := hAbs
        -- `re z ≥ -|z|` and `|z| ≤ δ`
        have hre : Complex.re ⟪(B - A) v, v⟫_ℂ ≥ -Complex.abs ⟪(B - A) v, v⟫_ℂ := by
          -- `|re z| ≤ |z|` ⇒ `- |z| ≤ re z`
          have habsre : |(Complex.re ⟪(B - A) v, v⟫_ℂ)| ≤ Complex.abs ⟪(B - A) v, v⟫_ℂ :=
            Complex.abs_re_le_abs _
          have : -(Complex.abs ⟪(B - A) v, v⟫_ℂ) ≤ Complex.re ⟪(B - A) v, v⟫_ℂ := by
            -- from `|re| ≤ |z|`
            exact (abs_le.mp habsre).1
          exact this
        linarith
      exact this
    -- conclude
    linarith [hEq, hRe_ge]
  -- Use the gap inequality for `A` on the orthogonal component `w`, and expand `v = (⟪u,v⟫)u + w`.
  have hAv_ge : Complex.re ⟪A v, v⟫_ℂ ≥ lam + g * ‖w‖ ^ 2 := by
    have hAsymm : (A : H →ₗ[ℂ] H).IsSymmetric :=
      (IsSelfAdjoint.isSymmetric (A := A) hGap.selfAdjoint)
    have hv_decomp : v = (⟪u, v⟫_ℂ) • u + w := by
      simp [w, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    have hw_mem : w ∈ (ℂ ∙ u)ᗮ := by
      -- `w ⟂ u` implies `w ∈ (ℂ ∙ u)ᗮ`.
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℂ) (u := u) (v := w)).2 huw
    have hAw_mem : A w ∈ (ℂ ∙ u)ᗮ := by
      -- Show `⟪u, A w⟫ = 0` using symmetry of `A` and the eigen relation `A u = lam • u`.
      have hsymm_uw : ⟪A u, w⟫_ℂ = ⟪u, A w⟫_ℂ :=
        LinearMap.IsSymmetric.apply_clm (T := A) hAsymm u w
      have : ⟪u, A w⟫_ℂ = 0 := by
        -- `⟪u, A w⟫ = ⟪A u, w⟫` by symmetry, and `A u = lam • u`, so this is `lam† * ⟪u,w⟫ = 0`.
        have h1 : ⟪u, A w⟫_ℂ = ⟪A u, w⟫_ℂ := by
          -- from `⟪A u, w⟫ = ⟪u, A w⟫`
          simpa [hsymm_uw] using hsymm_uw.symm
        have h2 : ⟪A u, w⟫_ℂ = ⟪(lam : ℂ) • u, w⟫_ℂ := by
          -- rewrite `A u` using the eigen relation
          simpa [hGap.eigen]
        calc
          ⟪u, A w⟫_ℂ = ⟪(lam : ℂ) • u, w⟫_ℂ := by simpa [h1] using h2
          _ = (star (lam : ℂ)) * ⟪u, w⟫_ℂ := by
                -- use the general `inner_smul_left` formula over `ℂ`
                -- (avoid the `ℝ`-specialized lemma that `simp` sometimes prefers)
                simpa using (inner_smul_left (𝕜 := ℂ) (x := u) (y := w) (r := (lam : ℂ)))
          _ = (star (lam : ℂ)) * 0 := by simpa [huw]
          _ = 0 := by simp
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℂ) (u := u) (v := A w)).2 this
    -- Now cross terms vanish because `A w ∈ (ℂ ∙ u)ᗮ`.
    have hcross : ⟪(⟪u, v⟫_ℂ) • u, A w⟫_ℂ = 0 := by
      -- `(ℂ ∙ u)` is orthogonal to `(ℂ ∙ u)ᗮ`
      have hu_mem : ((⟪u, v⟫_ℂ) • u) ∈ (ℂ ∙ u) := by
        exact (Submodule.mem_span_singleton).2 ⟨⟪u, v⟫_ℂ, by simp⟩
      exact Submodule.inner_right_of_mem_orthogonal hu_mem hAw_mem
    have hcross' : ⟪A ((⟪u, v⟫_ℂ) • u), w⟫_ℂ = 0 := by
      -- `A ((⟪u,v⟫)u)` is in the span, and `w ∈ (ℂ ∙ u)ᗮ`.
      have hu_mem : A ((⟪u, v⟫_ℂ) • u) ∈ (ℂ ∙ u) := by
        -- `A (c•u) = (c*lam)•u`
        refine (Submodule.mem_span_singleton).2 ?_
        refine ⟨(⟪u, v⟫_ℂ) * (lam : ℂ), ?_⟩
        simp [hGap.eigen, smul_smul, mul_smul, mul_assoc]
      exact Submodule.inner_right_of_mem_orthogonal hu_mem hw_mem
    -- Expand `re ⟪A v, v⟫` using `v = proj + w` and cancel cross terms.
    have hRe :
        Complex.re ⟪A v, v⟫_ℂ =
          Complex.re ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ + Complex.re ⟪A w, w⟫_ℂ := by
      -- expand using `hv_decomp`, without a simp explosion
      let proj : H := (⟪u, v⟫_ℂ) • u
      have : ⟪A v, v⟫_ℂ =
          ⟪A proj, proj⟫_ℂ
            + ⟪A proj, w⟫_ℂ
            + ⟪A w, proj⟫_ℂ
            + ⟪A w, w⟫_ℂ := by
        -- `v = proj + w`
        -- `A v = A proj + A w`
        -- then use `inner_add_add_self`
        have hv' : v = proj + w := by simpa [proj] using hv_decomp
        have hAv : A v = A proj + A w := by
          calc
            A v = A (proj + w) := by simpa [hv']
            _ = A proj + A w := by simpa using (map_add A proj w)
        -- now expand the inner product of a sum
        calc
          ⟪A v, v⟫_ℂ = ⟪A proj + A w, proj + w⟫_ℂ := by
              simpa [hv', hAv]
          _ = ⟪A proj, proj⟫_ℂ
                + ⟪A proj, w⟫_ℂ
                + ⟪A w, proj⟫_ℂ
                + ⟪A w, w⟫_ℂ := by
              -- bilinearity in each argument
              simp [inner_add_left, inner_add_right, add_assoc, add_left_comm, add_comm]
      -- take real parts and use the cross-term zeros (and symmetry for the other cross term)
      have h0 : ⟪A w, (⟪u, v⟫_ℂ) • u⟫_ℂ = 0 := by
        -- symmetry: ⟪A w, proj⟫ = ⟪w, A proj⟫, and `A proj ∈ span`, while `w ∈ spanᗮ`
        have := LinearMap.IsSymmetric.apply_clm (T := A) hAsymm w ((⟪u, v⟫_ℂ) • u)
        -- `this : ⟪A w, proj⟫ = ⟪w, A proj⟫`
        -- and `⟪w, A proj⟫ = 0` by orthogonality
        have hwAproj : ⟪w, A ((⟪u, v⟫_ℂ) • u)⟫_ℂ = 0 := by
          have hu_mem : A ((⟪u, v⟫_ℂ) • u) ∈ (ℂ ∙ u) := by
            refine (Submodule.mem_span_singleton).2 ?_
            refine ⟨(⟪u, v⟫_ℂ) * (lam : ℂ), ?_⟩
            simp [hGap.eigen, smul_smul, mul_smul, mul_assoc]
          exact Submodule.inner_left_of_mem_orthogonal hu_mem hw_mem
        exact by simpa [this] using hwAproj
      have := congrArg Complex.re this
      -- simplify using the cross-term zeros
      simpa [hcross', h0, add_assoc, add_left_comm, add_comm] using this
    -- Lower bound the `w` energy by the gap, and the `u`-component energy by `lam * ‖proj‖^2`.
    have hAw_ge : Complex.re ⟪A w, w⟫_ℂ ≥ (lam + g) * ‖w‖ ^ 2 := hGap.gap w huw
    -- `A (c•u) = (lam)•(c•u)` implies `re ⟪A (c•u), (c•u)⟫ = lam * ‖c•u‖^2`.
    have hAu_ge :
        Complex.re ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ = lam * ‖(⟪u, v⟫_ℂ) • u‖ ^ 2 := by
      -- rewrite `A (c•u)` using eigen relation and simplify.
      simp [hGap.eigen, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
        Complex.ofReal_re, mul_assoc, mul_left_comm, mul_comm]
    -- Use Pythagoras: `‖v‖^2 = ‖proj‖^2 + ‖w‖^2`.
    have hnorm_v_sq : ‖v‖ ^ 2 = ‖(⟪u, v⟫_ℂ) • u‖ ^ 2 + ‖w‖ ^ 2 := by
      have hw_proj0 : ⟪(⟪u, v⟫_ℂ) • u, w⟫_ℂ = 0 := by
        -- from `huw` and `inner_smul_left`
        simp [inner_smul_left, huw]
      have hpyth :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((⟪u, v⟫_ℂ) • u) w hw_proj0
      -- convert multiplicative form to `pow_two` and rewrite `v`.
      simpa [pow_two, hv_decomp] using hpyth
    -- Assemble the inequality.
    have : Complex.re ⟪A v, v⟫_ℂ ≥ lam + g * ‖w‖ ^ 2 := by
      calc
        Complex.re ⟪A v, v⟫_ℂ
            = (lam * ‖(⟪u, v⟫_ℂ) • u‖ ^ 2) + Complex.re ⟪A w, w⟫_ℂ := by
                -- use `hRe` and `hAu_ge`
                simpa [hAu_ge, add_comm, add_left_comm, add_assoc] using hRe
        _ ≥ (lam * ‖(⟪u, v⟫_ℂ) • u‖ ^ 2) + ((lam + g) * ‖w‖ ^ 2) := by
              gcongr
              exact hAw_ge
        _ = lam * (‖(⟪u, v⟫_ℂ) • u‖ ^ 2 + ‖w‖ ^ 2) + g * ‖w‖ ^ 2 := by ring
        _ = lam * ‖v‖ ^ 2 + g * ‖w‖ ^ 2 := by simpa [hnorm_v_sq] using rfl
        _ = lam + g * ‖w‖ ^ 2 := by simp [hnormv, pow_two]
    exact this
  -- Combine: (A v,v) is within ±δ of (B v,v), and (B v,v) ≤ (B u,u) ≤ (A u,u)+δ = λ+δ.
  have hupper : Complex.re ⟪A v, v⟫_ℂ ≤ lam + 2 * δ := by
    have hAuu : Complex.re ⟪A u, u⟫_ℂ = lam := by
      -- since `A u = lam u` and ‖u‖=1
      have : ⟪A u, u⟫_ℂ = (lam : ℂ) * ⟪u, u⟫_ℂ := by
        simpa [hGap.eigen, inner_smul_left, mul_assoc] using congrArg (fun z => ⟪z, u⟫_ℂ) hGap.eigen
      -- rewrite `⟪u,u⟫` and take real parts
      -- `inner_self_eq_norm_sq_to_K` gives `⟪u,u⟫ = ‖u‖^2`
      -- and `‖u‖=1`.
      simp [inner_self_eq_norm_sq_to_K, hGap.norm_u] at this
    -- use inequalities
    have : Complex.re ⟪A v, v⟫_ℂ ≤ Complex.re ⟪B v, v⟫_ℂ + δ := by
      -- from `hBv_ge` rearranged
      linarith [hBv_ge]
    have : Complex.re ⟪A v, v⟫_ℂ ≤ Complex.re ⟪B u, u⟫_ℂ + δ := by
      linarith [this, huv]
    have : Complex.re ⟪A v, v⟫_ℂ ≤ Complex.re ⟪A u, u⟫_ℂ + 2 * δ := by
      linarith [this, hBu_le]
    simpa [hAuu, two_mul] using this
  -- Now isolate `‖w‖^2`.
  have hg : g * ‖w‖ ^ 2 ≤ 2 * δ := by
    -- `λ + g‖w‖^2 ≤ re⟪A v,v⟫ ≤ λ + 2δ`
    have : lam + g * ‖w‖ ^ 2 ≤ lam + 2 * δ := le_trans hAv_ge hupper
    linarith
  -- divide by positive `g`
  have hgpos : 0 < g := hGap.gap_pos
  have : ‖w‖ ^ 2 ≤ (2 * δ) / g := by
    -- `g * ‖w‖^2 ≤ 2δ`
    have : ‖w‖ ^ 2 ≤ (2 * δ) / g := by
      have := (le_div_iff₀ hgpos).2 hg
      simpa [div_eq_mul_inv, mul_assoc] using this
    exact this
  -- finish: `w = v - ⟪u,v⟫ u`
  simpa [w]

end SpectralPerturbation

end ExplicitFormula
end RiemannRecognitionGeometry
