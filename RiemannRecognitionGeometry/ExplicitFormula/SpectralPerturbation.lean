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
import Mathlib.Data.Complex.Abs

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open scoped Real InnerProductSpace

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
  -- Use the gap inequality for `A` on the orthogonal component `w`.
  have hAv_ge : Complex.re ⟪A v, v⟫_ℂ ≥ lam + g * ‖w‖ ^ 2 := by
    -- Work with the orthogonal projection onto `ℂ ∙ u` and its complement.
    let U : Submodule ℂ H := (ℂ ∙ u)
    have hproj_eq : (orthogonalProjection U v : H) = (⟪u, v⟫_ℂ) • u := by
      -- Projection formula for a unit vector.
      simpa [U] using (orthogonalProjection_unit_singleton (𝕜 := ℂ) (v := u) hGap.norm_u v)
    -- Define the orthogonal component via projection.
    have hw_eq : w = v - (orthogonalProjection U v : H) := by
      -- `w = v - ⟪u,v⟫u` and `proj = ⟪u,v⟫u`.
      simp [w, hproj_eq]
    have hw_orth : w ∈ Uᗮ := by
      -- by definition of orthogonal projection
      -- `v - proj_U v ∈ Uᗮ`
      simpa [hw_eq] using (sub_orthogonalProjection_mem_orthogonal (K := U) v)
    have huw' : ⟪u, w⟫_ℂ = 0 := by
      -- `w ∈ (ℂ ∙ u)ᗮ` iff `⟪u, w⟫ = 0`.
      -- (`U = ℂ ∙ u` by definition.)
      simpa [U] using (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℂ) (u := u) (v := w)).1 hw_orth
    -- A is symmetric (since it is self-adjoint), so cross terms vanish in the orthogonal decomposition.
    have hAsymm : (A : H →ₗ[ℂ] H).IsSymmetric :=
      (IsSelfAdjoint.isSymmetric (A := A) hGap.selfAdjoint)
    -- First compute the energy of the projection piece using the eigenvector property.
    have hA_proj :
        Complex.re ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ =
          lam * ‖(⟪u, v⟫_ℂ) • u‖ ^ 2 := by
      -- `A (c•u) = c•A u = c•(λ•u)`
      calc
        Complex.re ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ
            = Complex.re ⟪((⟪u, v⟫_ℂ) • ((lam : ℂ) • u)), ((⟪u, v⟫_ℂ) • u)⟫_ℂ := by
                -- linearity of `A` and eigen relation
                simp [hGap.eigen, mul_smul, smul_smul]
        _ = Complex.re (((lam : ℂ) * ‖(⟪u, v⟫_ℂ) • u‖ ^ 2 : ℝ) : ℂ) := by
                -- inner of `((lam:ℂ)•x)` with `x` is `conj lam * ⟪x,x⟫`, but `lam` is real so `conj lam = lam`.
                -- We do this via `inner_smul_left` and `inner_self_eq_norm_sq_to_K`.
                have hlam : conj (lam : ℂ) = (lam : ℂ) := by simp
                -- simplify the inner product
                simp [inner_smul_left, hlam, inner_self_eq_norm_sq_to_K]
        _ = lam * ‖(⟪u, v⟫_ℂ) • u‖ ^ 2 := by
                -- `re ((lam:ℝ) : ℂ) = lam`
                simp [Complex.ofReal_re]
    -- Cross terms vanish: `⟪A w, proj⟫ = 0` and `⟪A proj, w⟫ = 0`.
    have hcross1 : ⟪A w, (⟪u, v⟫_ℂ) • u⟫_ℂ = 0 := by
      -- Use symmetry: ⟪A w, proj⟫ = ⟪w, A proj⟫ and `A proj ∈ span u`, while `w ⟂ u`.
      have hAu : A u = (lam : ℂ) • u := hGap.eigen
      have hAproj_mem : A ((⟪u, v⟫_ℂ) • u) ∈ (ℂ ∙ u) := by
        -- `A((c)u) = c(λu)` is in the span
        refine Submodule.smul_mem (Submodule.mem_span_singleton_self u) ?_
        -- show scalar exists: `((⟪u,v⟫)*(λ))`
        simp [hAu, smul_smul, mul_smul]
      -- Now `w ∈ (ℂ∙u)ᗮ` gives `⟪w, A proj⟫ = 0`.
      have hwAproj : ⟪w, A ((⟪u, v⟫_ℂ) • u)⟫_ℂ = 0 := by
        -- membership in orthogonal complement to the span
        -- use `Submodule.mem_orthogonal_singleton_iff_inner_right`
        have hw' : w ∈ (ℂ ∙ u)ᗮ := by
          -- `w = v - proj` is orthogonal part
          simpa [U] using hw_orth
        -- convert `A proj` into a scalar multiple of `u`
        rcases (Submodule.mem_span_singleton).1 hAproj_mem with ⟨c, hc⟩
        -- `⟪w, c•u⟫ = 0` since `w ⟂ u`
        -- first get `⟪w,u⟫ = 0` from `w ∈ (ℂ∙u)ᗮ`
        have hwu : ⟪w, u⟫_ℂ = 0 := by
          have : ⟪w, u⟫_ℂ = 0 := by
            -- unfold mem_orthogonal via singleton
            simpa [Submodule.mem_orthogonal_singleton_iff_inner_right] using hw' u (Submodule.mem_span_singleton_self u)
          exact this
        -- now apply `inner_smul_right`
        simpa [hc, inner_smul_right, hwu]
      -- Now symmetry.
      have := congrArg (fun z : ℂ => z) (hAsymm.apply_clm w ((⟪u, v⟫_ℂ) • u))
      -- `hAsymm` gives `⟪A w, proj⟫ = ⟪w, A proj⟫`.
      simpa [LinearMap.IsSymmetric, hAsymm.apply_clm] using (by
        -- directly:
        simpa using (by
          -- `apply_clm` already states the equality
          exact (LinearMap.IsSymmetric.apply_clm (T := A) hAsymm w ((⟪u, v⟫_ℂ) • u)).trans hwAproj))
    have hcross2 : ⟪A ((⟪u, v⟫_ℂ) • u), w⟫_ℂ = 0 := by
      -- Use symmetry again and `hcross1`.
      -- From symmetry: ⟪A proj, w⟫ = ⟪proj, A w⟫, and since `hcross1` is ⟪A w, proj⟫ = 0,
      -- we can flip via conjugate symmetry.
      have hsymm := (LinearMap.IsSymmetric.apply_clm (T := A) hAsymm ((⟪u, v⟫_ℂ) • u) w)
      -- `hsymm : ⟪A proj, w⟫ = ⟪proj, A w⟫`
      -- But `⟪proj, A w⟫ = conj ⟪A w, proj⟫ = 0`.
      have : ⟪(⟪u, v⟫_ℂ) • u, A w⟫_ℂ = 0 := by
        -- Use conjugate symmetry: `⟪proj, A w⟫ = conj ⟪A w, proj⟫`.
        have := congrArg conj hcross1
        -- `conj 0 = 0`
        simpa [inner_conj_symm] using this
      exact by simpa [hsymm] using this
    -- Now expand ⟪A v,v⟫ with `v = proj + w`.
    have hv_decomp : v = (⟪u, v⟫_ℂ) • u + w := by
      simp [w, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    -- Compute the real part using bilinearity and the vanished cross terms.
    have hRe :
        Complex.re ⟪A v, v⟫_ℂ =
          Complex.re ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ
            + Complex.re ⟪A w, w⟫_ℂ := by
      -- Expand using `hv_decomp`.
      -- We'll work in ℂ and then take `Complex.re`.
      -- Use `simp` to expand inner products and kill cross terms.
      have : ⟪A v, v⟫_ℂ =
          ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ
            + ⟪A ((⟪u, v⟫_ℂ) • u), w⟫_ℂ
            + ⟪A w, ((⟪u, v⟫_ℂ) • u)⟫_ℂ
            + ⟪A w, w⟫_ℂ := by
        -- direct expansion
        simp [hv_decomp, map_add, inner_add_left, inner_add_right, add_assoc, add_left_comm, add_comm]
      -- take real parts and cancel the zero cross terms
      -- `Complex.re` is additive.
      -- (Use `simp` for `map_add` and the cross-term zeros.)
      -- We'll rewrite and simp.
      have : Complex.re ⟪A v, v⟫_ℂ =
          Complex.re ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ
            + Complex.re ⟪A w, w⟫_ℂ := by
        -- start from the expanded equality
        -- `simp` should turn cross terms into 0 and combine.
        -- Use the previous `this` and apply `congrArg Complex.re`.
        have := congrArg Complex.re this
        -- simplify re of sums and the cross term zeros
        -- `Complex.re` is a ring hom, so `simp` will use `map_add`.
        simpa [hcross1, hcross2, add_assoc, add_left_comm, add_comm] using this
      exact this
    -- Now plug the gap bound for `w` and the eigen computation for the projection part.
    have hAw_ge : Complex.re ⟪A w, w⟫_ℂ ≥ (lam + g) * ‖w‖ ^ 2 := hGap.gap w huw'
    -- The projection part equals `λ * ‖proj‖^2`.
    -- Combine:
    -- `re⟪A v,v⟫ = re⟪A proj,proj⟫ + re⟪A w,w⟫ ≥ λ‖proj‖^2 + (λ+g)‖w‖^2
    --   = λ(‖proj‖^2+‖w‖^2) + g‖w‖^2 = λ‖v‖^2 + g‖w‖^2 = λ + g‖w‖^2`.
    have hproj_sq :
        Complex.re ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ = lam * ‖(⟪u, v⟫_ℂ) • u‖ ^ 2 :=
      hA_proj
    have hnorm_v_sq : ‖v‖ ^ 2 = (‖(⟪u, v⟫_ℂ) • u‖ ^ 2 + ‖w‖ ^ 2) := by
      -- Pythagoras: `v = proj + w` with orthogonality.
      have hw_proj0 : ⟪(⟪u, v⟫_ℂ) • u, w⟫_ℂ = 0 := by
        -- from `huw'` and `inner_smul_left`
        -- `⟪c•u, w⟫ = conj c * ⟪u,w⟫ = 0`.
        simp [inner_smul_left, huw']
      have hpyth :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((⟪u, v⟫_ℂ) • u) w hw_proj0
      -- rewrite `v = proj + w` and convert `‖x‖*‖x‖` to `‖x‖^2`.
      -- `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` gives `‖proj+w‖*‖proj+w‖ = ...`.
      -- We want `‖v‖^2 = ...`, so use `pow_two` and the equality.
      -- `‖x‖^2 = ‖x‖*‖x‖`.
      have : ‖(⟪u, v⟫_ℂ) • u + w‖ ^ 2 = ‖(⟪u, v⟫_ℂ) • u‖ ^ 2 + ‖w‖ ^ 2 := by
        -- from multiplicative form to `pow_two`.
        -- `‖x‖^2 = ‖x‖*‖x‖`
        -- So rewrite both sides.
        -- `hpyth : ‖proj+w‖*‖proj+w‖ = ‖proj‖*‖proj‖ + ‖w‖*‖w‖`
        -- Convert.
        simpa [pow_two] using hpyth
      -- now rewrite `v` using `hv_decomp`
      simpa [hv_decomp] using this
    -- Finally assemble.
    have : Complex.re ⟪A v, v⟫_ℂ ≥ lam + g * ‖w‖ ^ 2 := by
      calc
        Complex.re ⟪A v, v⟫_ℂ
            = Complex.re ⟪A ((⟪u, v⟫_ℂ) • u), ((⟪u, v⟫_ℂ) • u)⟫_ℂ
                + Complex.re ⟪A w, w⟫_ℂ := hRe
        _ ≥ (lam * ‖(⟪u, v⟫_ℂ) • u‖ ^ 2) + ((lam + g) * ‖w‖ ^ 2) := by
              gcongr
              · exact le_of_eq hproj_sq
              · exact hAw_ge
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
