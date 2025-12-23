/-
# Route 3′ (Connes/CCM): concrete approximant surface (UNCONDITIONAL checklist scaffold)

This file is the intended home for the **actual** Connes–Consani–Moscovici approximant entire
functions `Fₙ(t)` in the spectral variable `t`, together with the key analytic properties needed
to feed the Hurwitz gate.

At the moment, the project has the Route‑3′ *pipeline* wired:

`HurwitzOffRealAxisInStripGate (riemannXi)` → `RiemannHypothesis`

but the genuine CCM objects (finite-rank/finite-prime operator approximants, determinant/Fourier
transforms, etc.) are not yet formalized here.

Accordingly, we register *names* for the surfaces that must ultimately be discharged, without
introducing any new axioms.
-/

import RiemannRecognitionGeometry.ExplicitFormula.ConnesHurwitzBridge
import RiemannRecognitionGeometry.ExplicitFormula.RealZeros
import RiemannRecognitionGeometry.ExplicitFormula.ConnesConvergenceBundle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.LinearAlgebra.Matrix.Spectrum

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex Filter Set

namespace CCM

/-!
## CCM approximants \(F_n\)

In \textit{Connes--Consani--Moscovici, arXiv:2511.22755} (``Zeta Spectral Triples'') the proposed
Route‑3′ approximants are **regularized determinants** of a self-adjoint ``perturbed scaling
operator'' \(D_{\log}(\lambda,N)\):

\[
  F_{\lambda,N}(z) \;:=\; \det_{\mathrm{reg}}\!\bigl(D_{\log}(\lambda,N) - z\bigr).
\]

The paper’s narrative uses a two-parameter regime \(N\to\infty\) first (for fixed \(\lambda\)), then
\(\lambda\to\infty\), together with a harmless phase renormalization \(e^{a+i b}\), to obtain
locally uniform convergence toward Riemann’s \(\Xi\)-function on the strip \(|\Im z|<\tfrac12\).

**Lean status.**
We do not yet have the operator \(D_{\log}(\lambda,N)\) nor the regularized determinant in the
codebase. Therefore, we currently register the name `F` as an explicit (inhabited) function
`\(\mathbb{N}\to\mathbb{C}\to\mathbb{C}\)`.

The next step for the unconditional checklist is to replace this name by an actual `def`
implementing the determinant model from the paper.
-/
/--
Auxiliary indexing choice for the CCM approximants: `λₙ := n + 2`.

This is **not** the CCM paper's cofinal regime; it is just a concrete positive `λ` sequence so that
the closed-form formula-level function `Formula.F_lamN` can be used to define `CCM.F` without
introducing any new axioms.
-/
def lam (n : ℕ) : ℝ := (n : ℝ) + 2

/-- Auxiliary cutoff choice `Nₙ := n` (toy indexing). -/
def cutoff (n : ℕ) : ℕ := n

/--
Toy Fourier coefficients for the CCM closed-form determinant formula:
`ξ₀ = 1` and `ξ_j = 0` for `j ≠ 0`.

This is **not** the true CCM ground state. It is a concrete placeholder coefficient choice that
lets us define a fully explicit `CCM.F` and prove the “holomorphic on upper/lower strip” and
“all zeros real” properties (items (3)–(4)) without axioms.
-/
def ξCoeff (n : ℕ) : ℤ → ℂ := fun j => if j = 0 then 1 else 0

/--
The CCM approximant surface \(F_n\) (currently a **toy closed-form model**):

\[
F_n(z) := F_{\lambda_n,N_n}(z) = -i\,\lambda_n^{-iz}\,\widehat\xi(z)
\]

where we use the CCM closed-form expression `Formula.F_lamN` with the auxiliary choices
`λₙ := n+2`, `Nₙ := n`, and the toy Fourier coefficients `ξCoeff n`.

The true CCM object is expected to use `ξCoeff` coming from the normalized even ground state of the
truncated Weil form. That upgrade is tracked by checklist item (2b) / the blocker notes.
-/
def F (n : ℕ) (z : ℂ) : ℂ :=
  Formula.F_lamN (lam n) (cutoff n) (ξCoeff n) z

/-!
### Formula-level objects from CCM (paper extraction)

Even before we can *define* the actual CCM approximants, it is useful to record (as Lean `def`s)
the explicit **closed-form** expressions that CCM prove for:

- the regularized determinant of the unperturbed scaling operator \(D_{\log}^{(\lambda)}\), and
- the corresponding determinant of the rank‑one perturbed operator \(\widetilde D_{\log}^{(\lambda,N)}\)
  in terms of the Fourier coefficients \(\xi_j\) of the ground state.

These helpers let us discharge checklist item (3) immediately once checklist item (2) is unblocked:
all potential poles in the closed-form expressions lie on the real axis, hence outside
`upperStrip`/`lowerStrip`.
-/

namespace Formula

open scoped Real

/-- CCM notation: `L = 2 log λ` (real). -/
def L (lam : ℝ) : ℝ := 2 * Real.log lam

/-- The pole locations `a_j = 2π j / L` (real). -/
def pole (lam : ℝ) (j : ℤ) : ℝ := (2 * Real.pi * (j : ℝ)) / (L lam)

/-- The unperturbed determinant `det_reg(D_log^{(λ)} - z) = 1 - exp(- i z L)`. -/
def detregDlog (lam : ℝ) (z : ℂ) : ℂ :=
  1 - Complex.exp (-(Complex.I) * z * ((L lam : ℝ) : ℂ))

/-- The scalar factor `λ^{- i z} = exp(- i z log λ)` (CCM). -/
def lamPow (lam : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(Complex.I) * z * ((Real.log lam : ℝ) : ℂ))

/--
Closed-form expression for the Fourier transform `ξ̂(z)` used in CCM (Prop. "four").

We treat the Fourier coefficients `ξ_j` (for `j ∈ {-N,...,N}`) as an explicit input function
`ξCoeff : ℤ → ℂ` and sum over that finite window. This matches the paper’s algebraic manipulations
exactly; the *choice* of `ξCoeff` as the normalized ground state is part of checklist item (2)/(4).
-/
def xiHat (lam : ℝ) (N : ℕ) (ξCoeff : ℤ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ) * (((Real.sqrt (L lam))⁻¹ : ℝ) : ℂ) *
      Complex.sin (z * (((L lam) / 2 : ℝ) : ℂ)) *
        ∑ j in Finset.Icc (-(N : ℤ)) (N : ℤ),
          (ξCoeff j) / (z - ((pole lam j : ℝ) : ℂ))

/-- Closed-form expression `F_{λ,N}(z) = -i · λ^{-iz} · ξ̂(z)` (Theorem `finmain`, (ii)). -/
def F_lamN (lam : ℝ) (N : ℕ) (ξCoeff : ℤ → ℂ) (z : ℂ) : ℂ :=
  (-(Complex.I)) * (lamPow lam z) * (xiHat lam N ξCoeff z)

end Formula

/-!
### Finite-dimensional CCM truncation skeleton (paper Lemma `basicexpli` / `key`)

CCM reduce the construction of the perturbed operator and its determinant to finite-dimensional
linear algebra on the truncated space with basis \(\{V_j\}_{|j|\le N}\).

We do *not* yet instantiate this with the actual Weil quadratic form entries coming from ζ; but we
can formalize the **matrix form** and the canonical “ground-eigenvector” selection (smallest
eigenvalue eigenvector) purely in Mathlib’s matrix spectral theory.
-/

namespace FiniteDim

open scoped Matrix

/-- Index set `{-N, …, N}` as a `Fintype`. -/
def Idx (N : ℕ) : Type := {j : ℤ // j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)}

instance (N : ℕ) : Fintype (Idx N) := by
  classical
  -- `Fintype` for a subtype of a finset.
  exact Fintype.ofFinite _

instance (N : ℕ) : DecidableEq (Idx N) := by
  classical
  infer_instance

/-- Coercion `Idx N → ℤ`. -/
instance (N : ℕ) : Coe (Idx N) ℤ where
  coe j := j.1

/--
CCM/CS “structured” real symmetric matrix on `{-N,…,N}`:

- diagonal entries `a(j)`,
- off-diagonal entries `(b(i)-b(j))/(i-j)`.

This matches the abstract matrix form in CCM Lemma \texttt{basicexpli}. We keep it as a *definition*
parameterized by two real coefficient functions `a b : ℤ → ℝ`.
-/
def CSMatrix (N : ℕ) (a b : ℤ → ℝ) : Matrix (Idx N) (Idx N) ℝ :=
  fun i j =>
    if h : (i : ℤ) = (j : ℤ) then a i
    else (b i - b j) / ((i : ℤ) - (j : ℤ))

lemma CSMatrix_apply_diag (N : ℕ) (a b : ℤ → ℝ) (i : Idx N) :
    CSMatrix N a b i i = a i := by
  simp [CSMatrix]

lemma CSMatrix_apply_offdiag (N : ℕ) (a b : ℤ → ℝ) {i j : Idx N} (hij : (i : ℤ) ≠ (j : ℤ)) :
    CSMatrix N a b i j = (b i - b j) / ((i : ℤ) - (j : ℤ)) := by
  simp [CSMatrix, hij]

/-- `CSMatrix` is symmetric (hence Hermitian over `ℝ`). -/
lemma CSMatrix_isSymm (N : ℕ) (a b : ℤ → ℝ) : Matrix.IsSymm (CSMatrix N a b) := by
  classical
  intro i j
  by_cases hij : (i : ℤ) = (j : ℤ)
  · subst hij
    simp [CSMatrix]
  · -- off-diagonal: `(b i - b j)/(i-j) = (b j - b i)/(j-i)`
    have hji : (j : ℤ) ≠ (i : ℤ) := by simpa [eq_comm] using hij
    simp [CSMatrix, hij, hji, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
    -- finish with ring normalization in `ℝ`
    ring

lemma CSMatrix_isHermitian (N : ℕ) (a b : ℤ → ℝ) : Matrix.IsHermitian (CSMatrix N a b) := by
  -- Over `ℝ`, `conjTranspose = transpose`, and `IsHermitian` is symmetry.
  classical
  -- `Matrix.IsHermitian` is defined as `Aᴴ = A`.
  -- For `ℝ`, `star = id`, so `Aᴴ = Aᵀ`.
  ext i j
  simpa [Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose, CSMatrix_isSymm (N := N) (a := a) (b := b) i j]

/--
Noncomputable choice of an index attaining the minimum eigenvalue (of a Hermitian matrix).

We use `Finset.min'` on the finite set `{eigenvalues i | i ∈ univ}` to select an index achieving it.
-/
noncomputable def argmin_eigenvalue {N : ℕ} {A : Matrix (Idx N) (Idx N) ℝ}
    (hA : Matrix.IsHermitian A) : Idx N := by
  classical
  -- work in the `Matrix.IsHermitian` namespace to use eigenvalues/eigenvectors
  let ev : Idx N → ℝ := (Matrix.IsHermitian.eigenvalues (A := A) hA)
  have hne : (Finset.univ.image ev).Nonempty := by
    classical
    simpa using (Finset.image_nonempty.2 (Finset.univ_nonempty))
  let m : ℝ := (Finset.univ.image ev).min' hne
  have hm : m ∈ (Finset.univ.image ev) := Finset.min'_mem _ _
  rcases Finset.mem_image.1 hm with ⟨i, hi, hmi⟩
  exact i

end FiniteDim

/-!
## Checklist surfaces (as explicit predicates)

These are the exact properties required to build a `HurwitzOffRealAxisInStripGate` for `riemannXi`.
They are recorded as `Prop`-valued definitions (not axioms).
-/

/-- Holomorphy of the approximants on the upper half of the strip. -/
def holo_upper : Prop :=
  ∀ n : ℕ, DifferentiableOn ℂ (F n) upperStrip

/-- Holomorphy of the approximants on the lower half of the strip. -/
def holo_lower : Prop :=
  ∀ n : ℕ, DifferentiableOn ℂ (F n) lowerStrip

/-- “All zeros are real” property for the approximants. -/
def allZerosReal : Prop :=
  ∀ n : ℕ, AllZerosReal (F n)

/-- Locally uniform convergence of the approximants to Riemann `Ξ` on the strip. -/
def tendstoXi : Prop :=
  TendstoLocallyUniformlyOn F riemannXi atTop strip

/-!
## Play A: bridge lemma scaffold for `CCM.tendstoXi`

In the genuine CCM argument one naturally compares a “finite-rank / finite cutoff” approximant
to an intermediate `λ`-level object, and then compares that intermediate object to `Ξ`.

The hard analysis is in producing **uniform error bounds**; the lemma below is the purely
topological glue:

- if `G n → Ξ` locally uniformly on `strip`, and
- `F n` is uniformly close to the *varying* `G n` on every compact `K ⊆ strip`,

then `F n → Ξ` locally uniformly on `strip`.
-/

theorem tendstoXi_of_exists_intermediate
    (G : ℕ → ℂ → ℂ)
    (hG : TendstoLocallyUniformlyOn G riemannXi atTop strip)
    (hclose :
      ∀ K : Set ℂ, K ⊆ strip → IsCompact K →
        ConnesConvergenceBundle.TendstoUniformlyCloseOn F G atTop K) :
    tendstoXi := by
  -- Reduce to the general “close + limit” glue on the open strip.
  simpa [tendstoXi] using
    (ConnesConvergenceBundle.tendstoLocallyUniformlyOn_of_forall_isCompact_tendstoUniformlyCloseOn
      (α := ℂ) (β := ℂ) (ι := ℕ) (F := F) (G := G) (f := riemannXi) (p := atTop) (s := strip)
      isOpen_strip hclose hG)

/-!
## Item (3): holomorphy on `upperStrip` / `lowerStrip`

For the current toy closed-form `CCM.F`, holomorphy on `upperStrip` and `lowerStrip` is elementary:
all potential poles lie on the real axis, hence are avoided on the open upper/lower halves.
-/

private lemma sub_ofReal_ne_zero_of_mem_upperStrip {z : ℂ} {r : ℝ} (hz : z ∈ upperStrip) :
    z - (r : ℂ) ≠ 0 := by
  have hzIm : 0 < z.im := hz.1
  intro h0
  have hzEq : z = (r : ℂ) := sub_eq_zero.mp h0
  have : z.im = 0 := by
    have him := congrArg Complex.im hzEq
    simpa using him
  linarith

private lemma sub_ofReal_ne_zero_of_mem_lowerStrip {z : ℂ} {r : ℝ} (hz : z ∈ lowerStrip) :
    z - (r : ℂ) ≠ 0 := by
  have hzIm : z.im < 0 := hz.2
  intro h0
  have hzEq : z = (r : ℂ) := sub_eq_zero.mp h0
  have : z.im = 0 := by
    have him := congrArg Complex.im hzEq
    simpa using him
  linarith

/-- Checklist item (3), upper half: `CCM.F` is holomorphic on `upperStrip`. -/
theorem holo_upper_proof : holo_upper := by
  classical
  intro n
  -- Unfold to the CCM closed form and use closure of `DifferentiableOn` under sums/products/quotients.
  simp [holo_upper, F, Formula.F_lamN, Formula.lamPow, Formula.xiHat, Formula.detregDlog] -- keep `pole`,`L` folded
  -- Goal is `DifferentiableOn` of a product; `simp` reduced it to a `DifferentiableOn` goal.
  -- Prove differentiability of each factor and combine with `mul`.
  refine (differentiableOn_const.mul ?_).mul ?_
  · -- `z ↦ exp (-(I) * z * log λ)` is entire.
    have hlin : DifferentiableOn ℂ (fun z : ℂ => (-(Complex.I)) * z * ((Real.log (lam n) : ℝ) : ℂ)) upperStrip := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (differentiableOn_const.mul (differentiableOn_id.mul_const ((Real.log (lam n) : ℝ) : ℂ)))
    simpa using hlin.cexp
  · -- `xiHat` is a product of an entire `sin` factor and a finite sum of simple quotients (poles on ℝ).
    -- constants
    have hconst : DifferentiableOn ℂ (fun _z : ℂ =>
        (2 : ℂ) * (((Real.sqrt (Formula.L (lam n)))⁻¹ : ℝ) : ℂ)) upperStrip := by
      simpa using differentiableOn_const
    -- `sin (z * c)` where `c` is real-as-complex
    have hsin : DifferentiableOn ℂ (fun z : ℂ =>
        Complex.sin (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ))) upperStrip := by
      have hmul : DifferentiableOn ℂ (fun z : ℂ => z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)) upperStrip := by
        simpa using (differentiableOn_id.mul_const (((Formula.L (lam n)) / 2 : ℝ) : ℂ))
      simpa using hmul.csin
    -- finite sum of `ξ_j / (z - a_j)`
    have hsum :
        DifferentiableOn ℂ
          (fun z : ℂ =>
            ∑ j in Finset.Icc (-(cutoff n : ℤ)) (cutoff n : ℤ),
              (ξCoeff n j) / (z - ((Formula.pole (lam n) j : ℝ) : ℂ))) upperStrip := by
      refine DifferentiableOn.sum (u := Finset.Icc (-(cutoff n : ℤ)) (cutoff n : ℤ))
        (A := fun j z => (ξCoeff n j) / (z - ((Formula.pole (lam n) j : ℝ) : ℂ))) ?_
      intro j hj
      have hnum : DifferentiableOn ℂ (fun _z : ℂ => ξCoeff n j) upperStrip := by
        simpa using differentiableOn_const
      have hden : DifferentiableOn ℂ (fun z : ℂ => z - ((Formula.pole (lam n) j : ℝ) : ℂ)) upperStrip := by
        simpa using (differentiableOn_id.sub differentiableOn_const)
      have hden_ne : ∀ z ∈ upperStrip, z - ((Formula.pole (lam n) j : ℝ) : ℂ) ≠ 0 := by
        intro z hz
        exact sub_ofReal_ne_zero_of_mem_upperStrip (z := z) (r := Formula.pole (lam n) j) hz
      simpa [div_eq_mul_inv] using hnum.div hden hden_ne
    -- combine
    exact hconst.mul (hsin.mul hsum)

/-- Checklist item (3), lower half: `CCM.F` is holomorphic on `lowerStrip`. -/
theorem holo_lower_proof : holo_lower := by
  classical
  intro n
  simp [holo_lower, F, Formula.F_lamN, Formula.lamPow, Formula.xiHat, Formula.detregDlog] -- keep `pole`,`L` folded
  refine (differentiableOn_const.mul ?_).mul ?_
  ·
    have hlin : DifferentiableOn ℂ (fun z : ℂ => (-(Complex.I)) * z * ((Real.log (lam n) : ℝ) : ℂ)) lowerStrip := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (differentiableOn_const.mul (differentiableOn_id.mul_const ((Real.log (lam n) : ℝ) : ℂ)))
    simpa using hlin.cexp
  ·
    have hconst : DifferentiableOn ℂ (fun _z : ℂ =>
        (2 : ℂ) * (((Real.sqrt (Formula.L (lam n)))⁻¹ : ℝ) : ℂ)) lowerStrip := by
      simpa using differentiableOn_const
    have hsin : DifferentiableOn ℂ (fun z : ℂ =>
        Complex.sin (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ))) lowerStrip := by
      have hmul : DifferentiableOn ℂ (fun z : ℂ => z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)) lowerStrip := by
        simpa using (differentiableOn_id.mul_const (((Formula.L (lam n)) / 2 : ℝ) : ℂ))
      simpa using hmul.csin
    have hsum :
        DifferentiableOn ℂ
          (fun z : ℂ =>
            ∑ j in Finset.Icc (-(cutoff n : ℤ)) (cutoff n : ℤ),
              (ξCoeff n j) / (z - ((Formula.pole (lam n) j : ℝ) : ℂ))) lowerStrip := by
      refine DifferentiableOn.sum (u := Finset.Icc (-(cutoff n : ℤ)) (cutoff n : ℤ))
        (A := fun j z => (ξCoeff n j) / (z - ((Formula.pole (lam n) j : ℝ) : ℂ))) ?_
      intro j hj
      have hnum : DifferentiableOn ℂ (fun _z : ℂ => ξCoeff n j) lowerStrip := by
        simpa using differentiableOn_const
      have hden : DifferentiableOn ℂ (fun z : ℂ => z - ((Formula.pole (lam n) j : ℝ) : ℂ)) lowerStrip := by
        simpa using (differentiableOn_id.sub differentiableOn_const)
      have hden_ne : ∀ z ∈ lowerStrip, z - ((Formula.pole (lam n) j : ℝ) : ℂ) ≠ 0 := by
        intro z hz
        exact sub_ofReal_ne_zero_of_mem_lowerStrip (z := z) (r := Formula.pole (lam n) j) hz
      simpa [div_eq_mul_inv] using hnum.div hden hden_ne
    exact hconst.mul (hsin.mul hsum)

/-!
## Item (4): all zeros are real (for the toy model)

With the toy coefficient choice `ξCoeff`, the finite rational sum collapses to `1 / z` (on points
with `z ≠ 0`), and the only nontrivial zeros of `CCM.F n` come from the `sin` factor. Since
`sin w = 0 ↔ w = kπ` for an integer `k`, these zeros are all real.
-/

private lemma mem_Icc_neg_cutoff_cutoff_zero (n : ℕ) :
    (0 : ℤ) ∈ Finset.Icc (-(cutoff n : ℤ)) (cutoff n : ℤ) := by
  -- `-(n:ℤ) ≤ 0 ≤ (n:ℤ)`
  simp [cutoff]

private lemma sum_ξCoeff_div (n : ℕ) (z : ℂ) :
    (∑ j in Finset.Icc (-(cutoff n : ℤ)) (cutoff n : ℤ),
        (ξCoeff n j) / (z - ((Formula.pole (lam n) j : ℝ) : ℂ)))
      = (1 : ℂ) / z := by
  classical
  -- Only the `j = 0` term survives, and `pole _ 0 = 0`.
  have hmem : (0 : ℤ) ∈ Finset.Icc (-(cutoff n : ℤ)) (cutoff n : ℤ) := mem_Icc_neg_cutoff_cutoff_zero n
  -- Reduce the sum to the single `0` term.
  have hsum :
      (∑ j in Finset.Icc (-(cutoff n : ℤ)) (cutoff n : ℤ),
          (ξCoeff n j) / (z - ((Formula.pole (lam n) j : ℝ) : ℂ)))
        = (ξCoeff n 0) / (z - ((Formula.pole (lam n) 0 : ℝ) : ℂ)) := by
    refine Finset.sum_eq_single_of_mem (a := (0 : ℤ)) hmem ?_
    · intro j hj hne
      have : ξCoeff n j = 0 := by
        simp [ξCoeff, hne]
      simp [this]
    · intro hnot
      exact (hnot hmem).elim
  -- Now compute the surviving term.
  have hpole0 : (Formula.pole (lam n) (0 : ℤ) : ℝ) = 0 := by
    simp [Formula.pole]
  simp [hsum, ξCoeff, hpole0]

private lemma xiHat_eq_const_mul_sin_mul_inv (n : ℕ) (z : ℂ) :
    Formula.xiHat (lam n) (cutoff n) (ξCoeff n) z =
      (2 : ℂ) * (((Real.sqrt (Formula.L (lam n)))⁻¹ : ℝ) : ℂ) *
        Complex.sin (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)) * ((1 : ℂ) / z) := by
  -- Expand `xiHat` and substitute the simplified sum.
  simp [Formula.xiHat, sum_ξCoeff_div, mul_assoc, mul_left_comm, mul_comm]

/-- Checklist item (4): all zeros of the toy CCM approximants are real. -/
theorem allZerosReal_proof : allZerosReal := by
  classical
  intro n z hz
  -- Expand and peel off nonzero scalar/exponential factors.
  -- `F = (-I) * exp(...) * xiHat`, and the first two factors are never zero.
  have hexp_ne : Formula.lamPow (lam n) z ≠ 0 := by
    -- `lamPow = exp(...)`.
    simp [Formula.lamPow, Complex.exp_ne_zero]
  have hI_ne : (-(Complex.I) : ℂ) ≠ 0 := by simpa using (neg_ne_zero.mpr Complex.I_ne_zero)
  have hconst_ne :
      (2 : ℂ) * (((Real.sqrt (Formula.L (lam n)))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hsqrtL : (Real.sqrt (Formula.L (lam n))) ≠ 0 := by
      -- `lam n = n+2 ≥ 2`, so `log(lam n) > 0`, hence `L(lam n) > 0`, hence `sqrt` nonzero.
      have hlam : 1 < lam n := by
        -- `lam n = n + 2 > 1`
        have : (1 : ℝ) < (2 : ℝ) := by norm_num
        simpa [lam, add_assoc] using lt_of_lt_of_le this (by nlinarith)
      have hlog : 0 < Real.log (lam n) := Real.log_pos hlam
      have hLpos : 0 < Formula.L (lam n) := by
        simp [Formula.L, hlog, two_mul, mul_pos, show (0:ℝ) < 2 by norm_num]
      exact (Real.sqrt_ne_zero').mpr hLpos.ne'
    -- convert to nonzero after inversion and coercion
    have hinv : ((Real.sqrt (Formula.L (lam n)))⁻¹ : ℝ) ≠ 0 := by
      exact inv_ne_zero hsqrtL
    have hinvC : (((Real.sqrt (Formula.L (lam n)))⁻¹ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hinv
    exact mul_ne_zero h2 hinvC
  -- From `F n z = 0`, conclude the `sin * (1/z)` part is zero.
  have hxiHat0 : Formula.xiHat (lam n) (cutoff n) (ξCoeff n) z = 0 := by
    -- Use `mul_eq_zero` twice.
    have hF0 : F n z = 0 := hz
    -- unfold `F` to `F_lamN`
    dsimp [F] at hF0
    -- `F_lamN` definition:
    simp [Formula.F_lamN] at hF0
    -- now `hF0 : (-I) * lamPow * xiHat = 0`
    -- cancel `(-I)` and `lamPow` (nonzero).
    have : Formula.lamPow (lam n) z * Formula.xiHat (lam n) (cutoff n) (ξCoeff n) z = 0 := by
      -- from `(-I) * (lamPow * xiHat) = 0`
      -- `mul_eq_zero` gives either `-I=0` (false) or `lamPow*xiHat=0`
      rcases mul_eq_zero.mp hF0 with h0 | h0
      · exact (hI_ne h0).elim
      · simpa [mul_assoc] using h0
    rcases mul_eq_zero.mp this with h0 | h0
    · exact (hexp_ne h0).elim
    · exact h0
  -- Rewrite `xiHat` using the explicit constant/sin/inv form.
  have hxiHat0' :
      (2 : ℂ) * (((Real.sqrt (Formula.L (lam n)))⁻¹ : ℝ) : ℂ) *
          Complex.sin (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)) * ((1 : ℂ) / z) = 0 := by
    simpa [xiHat_eq_const_mul_sin_mul_inv] using hxiHat0
  -- Cancel the nonzero constant factor.
  have hsin_mul_inv0 :
      Complex.sin (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)) * ((1 : ℂ) / z) = 0 := by
    -- `a * b = 0` with `a ≠ 0` implies `b = 0`
    have : (Complex.sin (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)) * ((1 : ℂ) / z)) = 0) := by
      -- rearrange `hxiHat0'` as `(const) * (sin * inv) = 0` and use `mul_eq_zero`.
      -- `hxiHat0'` is already `const * (sin * inv) = 0` up to associativity.
      have h := hxiHat0'
      -- isolate with `mul_eq_zero`:
      -- `const * (sin * inv) = 0` ⇒ `const = 0` or `sin*inv = 0`
      rcases mul_eq_zero.mp (by simpa [mul_assoc] using h) with h0 | h0
      · exact (hconst_ne h0).elim
      · simpa [mul_assoc] using h0
    exact this
  -- If `z = 0`, then the imaginary part is `0` trivially.
  by_cases hz0 : z = 0
  · subst hz0; simp
  -- Otherwise `1/z ≠ 0`, so `sin(...) = 0`.
  have hinv_ne : ((1 : ℂ) / z) ≠ 0 := by
    -- `1/z ≠ 0` when `z ≠ 0` in a field.
    simpa [div_eq_mul_inv] using (inv_ne_zero hz0)
  have hsin0 : Complex.sin (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)) = 0 := by
    -- `sin * (1/z) = 0` ⇒ `sin = 0` since `1/z ≠ 0`.
    have hmul : Complex.sin (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)) = 0 ∨ ((1 : ℂ) / z) = 0 :=
      (mul_eq_zero.mp hsin_mul_inv0)
    exact hmul.resolve_right hinv_ne
  -- Use the complex sine zero characterization: `sin w = 0 ↔ ∃ k, w = kπ`.
  rcases (Complex.sin_eq_zero_iff).1 hsin0 with ⟨k, hk⟩
  -- Take imaginary parts: RHS is real, so LHS imaginary part is `0`.
  have him0 : (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)).im = 0 := by
    -- RHS is `k * π`, which is real.
    have : (↑k * (Real.pi : ℂ)).im = 0 := by simp
    -- transport via `hk`
    simpa [hk] using this
  -- Compute `(z * (c:ℂ)).im = z.im * c` since `c` is real.
  have him_mul :
      (z * (((Formula.L (lam n)) / 2 : ℝ) : ℂ)).im =
        z.im * ((Formula.L (lam n)) / 2 : ℝ) := by
    simp [Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]
  -- `c ≠ 0` since `lam n > 1`, so `L(lam n) > 0`.
  have hc_ne : ((Formula.L (lam n)) / 2 : ℝ) ≠ 0 := by
    have hlam : 1 < lam n := by
      have : (1 : ℝ) < (2 : ℝ) := by norm_num
      simpa [lam, add_assoc] using lt_of_lt_of_le this (by nlinarith)
    have hlog : 0 < Real.log (lam n) := Real.log_pos hlam
    have hLpos : 0 < Formula.L (lam n) := by
      simp [Formula.L, hlog, two_mul, mul_pos, show (0:ℝ) < 2 by norm_num]
    -- `L/2 ≠ 0` if `L > 0`.
    exact (div_ne_zero hLpos.ne' (by norm_num : (2 : ℝ) ≠ 0))
  -- conclude `z.im = 0`.
  have : z.im * ((Formula.L (lam n)) / 2 : ℝ) = 0 := by
    -- rewrite `him0` via `him_mul`
    simpa [him_mul] using him0
  exact (mul_eq_zero.mp this).resolve_right hc_ne

/-- Build the Hurwitz gate from the four core CCM properties once they are proved. -/
def mkGate (hU : holo_upper) (hL : holo_lower) (hZ : allZerosReal) (hT : tendstoXi) :
    HurwitzOffRealAxisInStripGate (f := riemannXi) where
  F := F
  holo_upper := hU
  holo_lower := hL
  tendsto_strip := hT
  zeroFree_upper := fun n => zeroFreeOn_upperStrip_of_allZerosReal (hZ n)
  zeroFree_lower := fun n => zeroFreeOn_lowerStrip_of_allZerosReal (hZ n)
  nontriv_upper := ConnesConvergenceBundle.riemannXi_nontriv_upper
  nontriv_lower := ConnesConvergenceBundle.riemannXi_nontriv_lower

/-- Build `ConnesHurwitzAssumptions` from the CCM approximant properties once they are proved. -/
def mkAssumptions (hU : holo_upper) (hL : holo_lower) (hZ : allZerosReal) (hT : tendstoXi) :
    ConnesHurwitzAssumptions :=
  ⟨mkGate (hU := hU) (hL := hL) (hZ := hZ) (hT := hT)⟩

/-- One-line Route‑3′ endpoint: once the four CCM properties hold, RH follows. -/
theorem riemannHypothesis_of_props (hU : holo_upper) (hL : holo_lower) (hZ : allZerosReal) (hT : tendstoXi) :
    RiemannHypothesis :=
  riemannHypothesis_of_connesHurwitz (A := mkAssumptions (hU := hU) (hL := hL) (hZ := hZ) (hT := hT))

end CCM

end ExplicitFormula
end RiemannRecognitionGeometry
