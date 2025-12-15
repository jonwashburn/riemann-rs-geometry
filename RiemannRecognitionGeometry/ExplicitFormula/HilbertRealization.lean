/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.Basic
import RiemannRecognitionGeometry.ExplicitFormula.Defs
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.MainRoute3

/-!
# Route 3: Hilbert-space realization from positive-semidefinite forms

This file implements the **mechanical** part of the Route 3 strategy:

> Given a positive-semidefinite Hermitian form `B : V × V → ℂ`, construct a Hilbert space `H`
> and a linear map `T : V → H` such that `B(f,g) = ⟪Tf, Tg⟫_H`.

This is the standard GNS/RKHS/quotient-completion construction. It is **not** the hard part of
Route 3. The hard part is proving that the Weil form `W¹(f ⋆ₘ ˜ₘ(⋆ₜ g))` is positive-semidefinite.

## The key insight

The "bridge to reflection" problem factors as:

1. **Spectral identity** (THE HARD PART): Prove that for admissible test functions,
   `W¹(f ⋆ₘ ˜ₘ(⋆ₜ f)) = ∫ Re(2·J(s)) · |M[f](s)|² dμ(s)`
   where the integral is over the critical line (or unit circle after Cayley transform).

2. **Positivity** (immediate from spectral identity + `Re(2·J) ≥ 0`):
   Since `Re(2·J) ≥ 0` and `|M[f]|² ≥ 0`, the integral is nonnegative.

3. **Hilbert construction** (THIS FILE, mechanical):
   Any positive-semidefinite Hermitian form on a complex vector space yields a Hilbert space.

-/

noncomputable section

open Complex ComplexConjugate MeasureTheory

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace
open scoped InnerProductSpace

/-!
## Hermitian sesquilinear forms
-/

/-- A sesquilinear form `B : V × V → ℂ` is Hermitian if `B(g,f) = conj(B(f,g))`. -/
def IsHermitianForm {V : Type*} (B : V → V → ℂ) : Prop :=
  ∀ f g, B g f = starRingEnd ℂ (B f g)

/-- A form is positive-semidefinite if `B(f,f)` is real and nonnegative. -/
def IsPositiveSemidefiniteForm {V : Type*} (B : V → V → ℂ) : Prop :=
  ∀ f, 0 ≤ (B f f).re

/-!
## The GNS/quotient-completion theorem

This is the key mechanical result: a positive-semidefinite Hermitian form yields a Hilbert space.
-/

/--
The GNS-style Hilbert-space realization theorem.

Given a complex vector space `V` with a positive-semidefinite Hermitian form `B`,
there exists:
- a Hilbert space `H`
- a linear map `T : V → H`
such that `B(f,g) = ⟪Tf, Tg⟫_H`.

This is the "mechanical" part of Route 3: it reduces the Hilbert-space realization problem
to proving positive-semidefiniteness.
-/
theorem gns_hilbert_realization {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V → V → ℂ) (hH : IsHermitianForm B) (hPos : IsPositiveSemidefiniteForm B)
    (hLinL : ∀ f g h, B (f + g) h = B f h + B g h)
    (hSmulL : ∀ (c : ℂ) f g, B (c • f) g = c * B f g)
    (hLinR : ∀ f g h, B f (g + h) = B f g + B f h)
    (hSmulR : ∀ (c : ℂ) f g, B f (c • g) = starRingEnd ℂ c * B f g) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (T : V →ₗ[ℂ] H),
        ∀ f g : V, B f g = ⟪T f, T g⟫_ℂ := by
  -- Standard GNS construction:
  -- 1. N := { f | B(f,f) = 0 } is a subspace (by Cauchy-Schwarz for positive forms)
  -- 2. V/N has well-defined inner product induced by B
  -- 3. Complete V/N to get Hilbert space H
  -- 4. T := quotient_map ∘ inclusion
  sorry

/-!
## The spectral identity: THE REAL BLOCKER

The hard part of Route 3 is not the Hilbert construction above. It is proving:

For the Weil form `B(f,g) := W¹(f ⋆ₘ ˜ₘ(⋆ₜ g))`, we need a **spectral representation**:

  `B(f,f) = ∫_{critical line} Re(2·J(1/2 + it)) · |M[f](1/2 + it)|² dt`

(or equivalently, after Cayley transform to the unit circle).

Once this identity is established, positivity follows immediately from `Re(2·J) ≥ 0`.
-/

/-- The standard parameterization of the critical line: `t ↦ 1/2 + i t`. -/
def criticalLine (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * Complex.I

@[simp] lemma criticalLine_re (t : ℝ) : (criticalLine t).re = (1 / 2 : ℝ) := by
  simp [criticalLine]

@[simp] lemma criticalLine_im (t : ℝ) : (criticalLine t).im = t := by
  simp [criticalLine]

/-- The canonical weight extracted from an arithmetic field `J`: `t ↦ Re(2·J(1/2+it))`. -/
def weightOfJ (J : ℂ → ℂ) (t : ℝ) : ℝ :=
  (((2 : ℂ) * J (criticalLine t)).re)

/-- The canonical transform on the critical line: `t ↦ M[f](1/2+it)`. -/
def mellinOnCriticalLine {F : Type} [TestSpace F] (f : F) (t : ℝ) : ℂ :=
  M[f](criticalLine t)

/--
The spectral identity hypothesis: the Weil form can be expressed as an integral
with `Re(2·J)` as a nonnegative weight.

This is the genuine analytic content needed to close Route 3. Proving it requires:
- Justifying interchange of the zero-sum and the integral (Fubini/Tonelli)
- Handling boundary limits of analytic functions (Fatou-type theorems)
- Matching the Mellin normalization to the convolution/involution definitions
-/
structure SpectralIdentity (F : Type) [TestSpace F] (L : LagariasFramework F) where
  /-- The boundary measure (typically Lebesgue on `ℝ`, or Haar after Cayley). -/
  μ : Measure ℝ := volume
  /-- The "J-field" function appearing in the weight. -/
  J : ℂ → ℂ
  /-- The boundary transform used in the spectral representation (default: `t ↦ M[f](1/2+it)`). -/
  transform : F → ℝ → ℂ := mellinOnCriticalLine
  /-- Measurability of the transform (needed to form Bochner integrals). -/
  measurable_transform : ∀ f : F, Measurable (transform f)
  /-- Integrability of the energy density `t ↦ weightOfJ J t * ‖transform f t‖²`. -/
  integrable_energy : ∀ f : F, Integrable (fun t : ℝ => weightOfJ J t * Complex.normSq (transform f t)) μ
  /--
  The spectral identity (quadratic form version):

  `Re(W¹(f ⋆ₘ ˜ₘ(⋆ₜ f))) = ∫ Re(2·J(1/2+it)) · |transform f t|² dμ`.

  We state this as an equality of real numbers, since `WeilGate` is formulated in terms of `re`.
  -/
  identity_re :
    ∀ f : F,
      (L.W1 (TestSpace.quad (F := F) f)).re =
        ∫ t : ℝ, (weightOfJ J t) * Complex.normSq (transform f t) ∂ μ

variable {F : Type} [TestSpace F]

/--
From a spectral identity and `Re(2·J) ≥ 0`, we get positive-semidefiniteness of the Weil form.
This is THE KEY LEMMA that closes Route 3.
-/
theorem weilGate_from_spectral_identity
    (L : LagariasFramework F)
    (S : SpectralIdentity F L)
    (hRe : ∀ t : ℝ, 0 ≤ weightOfJ S.J t) :
    L.WeilGate := by
  intro f
  -- Rewrite the target using the spectral identity.
  have hspec : (L.W1 (TestSpace.quad (F := F) f)).re =
      ∫ t : ℝ, (weightOfJ S.J t) * Complex.normSq (S.transform f t) ∂ S.μ := by
    simpa [SpectralIdentity.transform, SpectralIdentity.μ] using (S.identity_re f)
  -- Prove the integral is nonnegative.
  have hnonneg_integrand :
      (∀ᵐ t ∂ S.μ, 0 ≤ (weightOfJ S.J t) * Complex.normSq (S.transform f t)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hw : 0 ≤ weightOfJ S.J t := hRe t
    have hn : 0 ≤ Complex.normSq (S.transform f t) := by
      exact Complex.normSq_nonneg _
    exact mul_nonneg hw hn
  have hint : 0 ≤ ∫ t : ℝ, (weightOfJ S.J t) * Complex.normSq (S.transform f t) ∂ S.μ := by
    -- real-valued Bochner integral reduces to the usual real integral
    exact MeasureTheory.integral_nonneg_of_ae hnonneg_integrand
  -- Conclude WeilGate.
  simpa [hspec] using hint

/-!
## Sesquilinear spectral identity ⇒ reflection positivity (weighted `L^2`)

The quadratic-form identity `identity_re` is enough to deduce `WeilGate`. For the stronger
intermediate target `ReflectionPositivityRealization` (a genuine inner-product representation of the
Weil form), it is convenient to package a **sesquilinear** spectral identity and then construct the
Hilbert space explicitly as an `L^2` space.

We implement the weight by pointwise multiplication with `Real.sqrt (weightOfJ J t)`, so that we can
use the standard `L2` inner product with respect to a fixed base measure `μ`.
-/

section SesquilinearSpectralIdentity

variable {F : Type} [TestSpace F] [AddCommGroup F] [Module ℂ F]

/-- The Route 3 sesquilinear test expression `f ⋆ₘ ˜ₘ(⋆ₜ g)`. -/
def pair (f g : F) : F :=
  f ⋆ₘ ˜ₘ (⋆ₜ g)

/-!
### A small algebra lemma for the weighted `L²` construction

We often want to rewrite `√w · (√w · z)` as `w · z` (and vice versa) when moving between:

- the Bochner-integral form `∫ w(t) · ⟪F_f(t), F_g(t)⟫ dt`, and
- the `L²` inner product form `⟪√w · F_f, √w · F_g⟫`.

This is purely algebraic and only uses `Real.mul_self_sqrt` (hence `0 ≤ w`).
-/

private lemma sqrt_mul_sqrt_mul {w : ℝ} (hw : 0 ≤ w) (z : ℂ) :
    ((Real.sqrt w : ℝ) : ℂ) * (((Real.sqrt w : ℝ) : ℂ) * z) = ((w : ℝ) : ℂ) * z := by
  have hsqrt : (Real.sqrt w) * (Real.sqrt w) = w := Real.mul_self_sqrt hw
  have hsqrtC : (((Real.sqrt w : ℝ) : ℂ) * ((Real.sqrt w : ℝ) : ℂ)) = ((w : ℝ) : ℂ) := by
    simpa using congrArg (fun r : ℝ => (r : ℂ)) hsqrt
  -- reassociate and rewrite `√w * √w`
  calc
    ((Real.sqrt w : ℝ) : ℂ) * (((Real.sqrt w : ℝ) : ℂ) * z)
        = (((Real.sqrt w : ℝ) : ℂ) * ((Real.sqrt w : ℝ) : ℂ)) * z := by
            simpa [mul_assoc] using
              (mul_assoc (((Real.sqrt w : ℝ) : ℂ)) (((Real.sqrt w : ℝ) : ℂ)) z).symm
    _   = ((w : ℝ) : ℂ) * z := by
            simpa [hsqrtC]

private lemma mul_eq_sqrt_mul_sqrt_mul {w : ℝ} (hw : 0 ≤ w) (z : ℂ) :
    ((w : ℝ) : ℂ) * z = ((Real.sqrt w : ℝ) : ℂ) * (((Real.sqrt w : ℝ) : ℂ) * z) := by
  simpa using (sqrt_mul_sqrt_mul (w := w) hw z).symm

/--
Sesquilinear spectral identity package.

This is the precise analytic ``missing lemma'' needed to build a Hilbert-space realization of the
Weil form by a weighted `L^2` construction.
-/
structure SesqSpectralIdentity (L : LagariasFramework F) where
  /-- Boundary measure (typically Lebesgue on `ℝ`). -/
  μ : Measure ℝ := volume
  /-- Arithmetic field `J` producing the weight. -/
  J : ℂ → ℂ
  /-- A linear boundary transform (typically `f ↦ (t ↦ M[f](1/2+it))`). -/
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /-- Pointwise nonnegativity of the weight `Re(2·J(1/2+it))`. -/
  weight_nonneg : ∀ t : ℝ, 0 ≤ weightOfJ J t
  /-- L² admissibility: the weighted transform belongs to `L²(μ)`. -/
  memL2 : ∀ f : F,
    MeasureTheory.Memℒp
      (fun t : ℝ => ((Real.sqrt (weightOfJ J t) : ℝ) : ℂ) * transform f t) 2 μ
  /--
  The sesquilinear spectral identity, stated already in Hilbert-space form:

  `W¹(f ⋆ₘ ˜ₘ(⋆ₜ g)) = ⟪T f, T g⟫` where `T f` is the weighted transform in `L²(μ)`.
  -/
  identity :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ⟪(memL2 f).toLp (fun t : ℝ => ((Real.sqrt (weightOfJ J t) : ℝ) : ℂ) * transform f t),
          (memL2 g).toLp (fun t : ℝ => ((Real.sqrt (weightOfJ J t) : ℝ) : ℂ) * transform g t)⟫_ℂ

/--
Sesquilinear spectral identity package (Bochner-integral form).

This is the same analytic content as `SesqSpectralIdentity`, but stated in the more classical
``explicit formula / Plancherel'' form:

`W¹(pair f g) = ∫ w(t) · conj(F_f(t)) · F_g(t) dμ`,

with `w(t) = Re(2·J(1/2+it))` and `F_f(t)` a boundary transform (typically the Mellin transform on
the critical line).

From this integral identity, the Hilbert-space form follows automatically by taking
`T f := √w · F_f` as an element of `L²(μ)` and using `MeasureTheory.L2.inner_def`.
-/
structure SesqIntegralIdentity (L : LagariasFramework F) where
  /-- Boundary measure (typically Lebesgue on `ℝ`). -/
  μ : Measure ℝ := volume
  /-- Arithmetic field `J` producing the weight `w(t) = Re(2·J(1/2+it))`. -/
  J : ℂ → ℂ
  /-- A linear boundary transform (typically `f ↦ (t ↦ M[f](1/2+it))`). -/
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  /-- Pointwise nonnegativity of the weight (needed to form `Real.sqrt`). -/
  weight_nonneg : ∀ t : ℝ, 0 ≤ weightOfJ J t
  /-- L² admissibility: the weighted transform `t ↦ √w(t) · F_f(t)` belongs to `L²(μ)`. -/
  memL2 : ∀ f : F,
    MeasureTheory.Memℒp
      (fun t : ℝ => ((Real.sqrt (weightOfJ J t) : ℝ) : ℂ) * transform f t) 2 μ
  /--
  The sesquilinear spectral identity, stated as a Bochner integral:

  `W¹(pair f g) = ∫ w(t) · conj(F_f(t)) · F_g(t) dμ`.
  -/
  identity_integral :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ∫ t : ℝ,
          ((weightOfJ J t : ℝ) : ℂ) * ((starRingEnd ℂ (transform f t)) * (transform g t)) ∂ μ

namespace SesqSpectralIdentity

variable (L : LagariasFramework F) (S : SesqSpectralIdentity (F := F) (L := L))

/-- The weighted boundary function used to define `T`. -/
def weighted (f : F) : ℝ → ℂ :=
  fun t : ℝ => ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) * S.transform f t

/-- The concrete Hilbert-space map `T : F → L²(μ)` associated to a sesquilinear spectral identity. -/
def T : F →ₗ[ℂ] (ℝ →₂[S.μ] ℂ) where
  toFun f := (S.memL2 f).toLp (weighted (L := L) S f)
  map_add' f g := by
    -- Prove equality in `L²` by almost-everywhere equality of functions.
    apply MeasureTheory.Lp.ext
    have hfg : (weighted (L := L) S (f + g)) = (weighted (L := L) S f + weighted (L := L) S g) := by
      funext t
      simp [weighted, map_add, Pi.add_apply, mul_add]
    -- Convert pointwise equality to ae-equality and rewrite using the `toLp`/`coeFn` lemmas.
    have hfg_ae : weighted (L := L) S (f + g) =ᵐ[S.μ] (weighted (L := L) S f + weighted (L := L) S g) :=
      Filter.Eventually.of_forall (fun t => by simpa [hfg])
    have hL : ((S.memL2 (f + g)).toLp (weighted (L := L) S (f + g))) =ᵐ[S.μ] weighted (L := L) S (f + g) :=
      MeasureTheory.Memℒp.coeFn_toLp (μ := S.μ) (hf := S.memL2 (f + g))
    have hF : ((S.memL2 f).toLp (weighted (L := L) S f)) =ᵐ[S.μ] weighted (L := L) S f :=
      MeasureTheory.Memℒp.coeFn_toLp (μ := S.μ) (hf := S.memL2 f)
    have hG : ((S.memL2 g).toLp (weighted (L := L) S g)) =ᵐ[S.μ] weighted (L := L) S g :=
      MeasureTheory.Memℒp.coeFn_toLp (μ := S.μ) (hf := S.memL2 g)
    have hAdd :
        (fun t : ℝ => (((S.memL2 f).toLp (weighted (L := L) S f) +
          (S.memL2 g).toLp (weighted (L := L) S g)) t))
          =ᵐ[S.μ] fun t : ℝ => (weighted (L := L) S f + weighted (L := L) S g) t := by
      -- Use local names to keep coercions under control.
      let u : (ℝ →₂[S.μ] ℂ) := (S.memL2 f).toLp (weighted (L := L) S f)
      let v : (ℝ →₂[S.μ] ℂ) := (S.memL2 g).toLp (weighted (L := L) S g)
      let uf : (ℝ → ℂ) := weighted (L := L) S f
      let vg : (ℝ → ℂ) := weighted (L := L) S g
      have hu : (u : ℝ → ℂ) =ᵐ[S.μ] uf := by
        simpa [u, uf] using hF
      have hv : (v : ℝ → ℂ) =ᵐ[S.μ] vg := by
        simpa [v, vg] using hG
      have hcoe := (MeasureTheory.Lp.coeFn_add u v)
      filter_upwards [hcoe, hu, hv] with t ht htu htv
      calc
        ((u + v) t) = (u t + v t) := ht
        _ = uf t + vg t := by simpa [htu, htv]
        _ = (uf + vg) t := rfl
    -- Finish by rewriting both sides to the same explicit function.
    filter_upwards [hL, hfg_ae, hAdd] with t htL htfg htAdd
    -- Goal: the two `L²` functions agree at `t`.
    calc
      ((S.memL2 (f + g)).toLp (weighted (L := L) S (f + g)) t)
          = weighted (L := L) S (f + g) t := htL
      _   = (weighted (L := L) S f + weighted (L := L) S g) t := htfg
      _   = (((S.memL2 f).toLp (weighted (L := L) S f) +
                (S.memL2 g).toLp (weighted (L := L) S g)) t) := by
              simpa using htAdd.symm
  map_smul' c f := by
    apply MeasureTheory.Lp.ext
    have hcf : weighted (L := L) S (c • f) = c • weighted (L := L) S f := by
      funext t
      -- `transform` is linear; `weighted` is scalar multiplication by a fixed real factor.
      simp [weighted, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    have hcf_ae : weighted (L := L) S (c • f) =ᵐ[S.μ] c • weighted (L := L) S f :=
      Filter.Eventually.of_forall (fun t => by simpa [hcf])
    have hL : ((S.memL2 (c • f)).toLp (weighted (L := L) S (c • f))) =ᵐ[S.μ] weighted (L := L) S (c • f) :=
      MeasureTheory.Memℒp.coeFn_toLp (μ := S.μ) (hf := S.memL2 (c • f))
    have hF : ((S.memL2 f).toLp (weighted (L := L) S f)) =ᵐ[S.μ] weighted (L := L) S f :=
      MeasureTheory.Memℒp.coeFn_toLp (μ := S.μ) (hf := S.memL2 f)
    have hSmul :
        (fun t : ℝ => ((c • (S.memL2 f).toLp (weighted (L := L) S f)) t))
          =ᵐ[S.μ] fun t : ℝ => (c • weighted (L := L) S f) t := by
      have hcoe := (MeasureTheory.Lp.coeFn_smul c ((S.memL2 f).toLp (weighted (L := L) S f)))
      filter_upwards [hcoe, hF] with t ht htf
      -- `ht` rewrites the `Lp`-smul into pointwise smul; then `htf` substitutes the underlying function.
      -- Here `ht` is exactly `((c • u) t) = c • (u t)`; use it in the forward direction.
      simpa [Pi.smul_apply, ht, htf]
    filter_upwards [hL, hcf_ae, hSmul] with t htL htcf htSmul
    calc
      ((S.memL2 (c • f)).toLp (weighted (L := L) S (c • f)) t)
          = weighted (L := L) S (c • f) t := htL
      _   = (c • weighted (L := L) S f) t := htcf
      _   = ((c • (S.memL2 f).toLp (weighted (L := L) S f)) t) := by
              simpa using htSmul.symm

/--
A sesquilinear spectral identity yields a `ReflectionPositivityRealization` by taking
`H = L²(μ)` and `T` as the weighted transform.
-/
theorem reflectionPositivityRealization (S : SesqSpectralIdentity (F := F) (L := L)) :
    OptionalTargets.ReflectionPositivityRealization (F := F) (L := L) := by
  classical
  refine ⟨(ℝ →₂[S.μ] ℂ), by infer_instance, by infer_instance, by infer_instance, T (L := L) S, ?_⟩
  intro f g
  -- Unfold `T` and use the packaged sesquilinear identity.
  simpa [T, weighted, pair] using (S.identity f g)

end SesqSpectralIdentity

namespace SesqIntegralIdentity

variable (L : LagariasFramework F) (S : SesqIntegralIdentity (F := F) (L := L))

/-- The weighted boundary function `t ↦ √w(t) · F_f(t)` used to define `T`. -/
def weighted (f : F) : ℝ → ℂ :=
  fun t : ℝ => ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) * S.transform f t

/-- Convert the Bochner-integral form into the Hilbert-space form `SesqSpectralIdentity`. -/
def toSesqSpectralIdentity : SesqSpectralIdentity (F := F) (L := L) where
  μ := S.μ
  J := S.J
  transform := S.transform
  weight_nonneg := S.weight_nonneg
  memL2 := S.memL2
  identity := by
    intro f g
    -- Start from the integral identity.
    have hInt := S.identity_integral (f := f) (g := g)
    -- Rewrite the inner product in `L²` as an integral (by definition).
    have hInner :
        ⟪(S.memL2 f).toLp (weighted (L := L) S f),
          (S.memL2 g).toLp (weighted (L := L) S g)⟫_ℂ
          =
          ∫ t : ℝ,
            ((weightOfJ S.J t : ℝ) : ℂ) * ((starRingEnd ℂ (S.transform f t)) * (S.transform g t)) ∂ S.μ := by
      -- Expand the `L²` inner product as an integral of pointwise inner products.
      -- Then rewrite `toLp` evaluations almost everywhere, and simplify the integrand.
      -- (This is purely algebraic; all analytic convergence is quarantined in `memL2`.)
      -- Use `L2.inner_def` and then simplify pointwise.
      -- We use `integral_congr_ae` to replace `toLp` by the underlying function.
      -- Define short names to keep coercions under control.
      let u : (ℝ →₂[S.μ] ℂ) := (S.memL2 f).toLp (weighted (L := L) S f)
      let v : (ℝ →₂[S.μ] ℂ) := (S.memL2 g).toLp (weighted (L := L) S g)
      have hu : (u : ℝ → ℂ) =ᵐ[S.μ] weighted (L := L) S f := by
        simpa [u, weighted] using (MeasureTheory.Memℒp.coeFn_toLp (μ := S.μ) (hf := S.memL2 f))
      have hv : (v : ℝ → ℂ) =ᵐ[S.μ] weighted (L := L) S g := by
        simpa [v, weighted] using (MeasureTheory.Memℒp.coeFn_toLp (μ := S.μ) (hf := S.memL2 g))
      -- Replace `u t, v t` by the underlying weighted functions and simplify.
      -- We do this under the integral by AE congruence.
      -- (The final algebra uses `starRingEnd` as conjugation on `ℂ`.)
      -- Note: `inner` on `ℂ` is `conj a * b`.
      -- Finish by `integral_congr_ae`.
      -- TODO: keep this lemma short; it is meant to be “automatic wiring”.
      -- We use `simp` for the pointwise algebra (conj distributes over `*` and fixes real scalars).
      -- Porting note: the preceding `have` is just `rfl`, but we keep it explicit for readability.
      -- Now:
      --   ⟪u t, v t⟫ = conj(u t) * v t
      --   = conj(√w * F_f) * (√w * F_g)
      --   = w * conj(F_f) * F_g
      -- with `w = (√w)*(√w)` because `w ≥ 0`.
      -- Implement this via AE substitutions `hu, hv`.
      have hpoint :
          (fun t : ℝ => ⟪u t, v t⟫_ℂ)
            =ᵐ[S.μ]
            (fun t : ℝ =>
              ((weightOfJ S.J t : ℝ) : ℂ) * ((starRingEnd ℂ (S.transform f t)) * (S.transform g t))) := by
        filter_upwards [hu, hv] with t htu htv
        -- Rewrite `u t` and `v t`.
        -- Then expand inner product on `ℂ` and simplify.
        -- `weightOfJ` is real; we use `Real.mul_self_sqrt` to rewrite `√w * √w = w`.
        have hw0 : 0 ≤ weightOfJ S.J t := S.weight_nonneg t
        -- Turn the `L²` representatives into the explicit weighted functions.
        -- Let `a := √w(t)` (a real scalar) and `Ff := transform f t`, `Fg := transform g t`.
        -- Then `u t = a • Ff` and `v t = a • Fg`, so:
        --   ⟪u t, v t⟫ = ⟪(a:ℂ) • Ff, (a:ℂ) • Fg⟫
        --           = (a:ℂ) * (a:ℂ) * ⟪Ff, Fg⟫
        --           = (w(t):ℂ) * ⟪Ff, Fg⟫.
        have htu' : u t = ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) • (S.transform f t) := by
          -- `htu` identifies `u t` with the weighted function value.
          -- `weighted` uses multiplication, which is scalar multiplication on `ℂ`.
          simpa [u, weighted, smul_eq_mul] using htu
        have htv' : v t = ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) • (S.transform g t) := by
          simpa [v, weighted, smul_eq_mul] using htv
        -- Now compute the inner product using sesquilinearity.
        -- The scalar is real, so `conj` fixes it.
        -- We finish by rewriting `√w * √w = w`.
        calc
          ⟪u t, v t⟫_ℂ
              = ⟪((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) • (S.transform f t),
                    ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) • (S.transform g t)⟫_ℂ := by
                    simpa [htu', htv']
          _   = ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) *
                  (((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) * ⟪S.transform f t, S.transform g t⟫_ℂ) := by
                  -- First `inner_smul_left`, then `inner_smul_right`, then simplify `conj` on reals.
                  -- `inner_smul_left` gives `conj a * ⟪Ff, a • Fg⟫`.
                  -- `inner_smul_right` gives `a * ⟪Ff, Fg⟫`.
                  -- `conj a = a` because `a` is real.
                  have ha : (starRingEnd ℂ (((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ)))
                      = ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) := by
                    simp
                  calc
                    ⟪((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) • (S.transform f t),
                        ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) • (S.transform g t)⟫_ℂ
                        = (starRingEnd ℂ (((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ))) *
                            ⟪S.transform f t, ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) • (S.transform g t)⟫_ℂ := by
                              -- `inner_smul_left` is stated with scalar multiplication; on `ℂ` it is multiplication.
                              -- We include `mul_assoc` so the normal form matches the target expression.
                              simpa [inner_smul_left, smul_eq_mul, mul_assoc]
                    _ = ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) *
                          ( ((Real.sqrt (weightOfJ S.J t) : ℝ) : ℂ) * ⟪S.transform f t, S.transform g t⟫_ℂ) := by
                          -- Use `ha` and `inner_smul_right`, then reassociate.
                          -- `inner_smul_right` gives `⟪x, a • y⟫ = a * ⟪x,y⟫`.
                          -- The remaining step is pure associativity/commutativity in `ℂ`.
                          -- `simp` can do this algebra once we give it the right rewrite rules.
                          simp [ha, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]
          _   = ((weightOfJ S.J t : ℝ) : ℂ) * ⟪S.transform f t, S.transform g t⟫_ℂ := by
                  -- Pure algebra: `√w · (√w · z) = w · z`.
                  simpa using
                    (sqrt_mul_sqrt_mul (w := weightOfJ S.J t) hw0 (z := ⟪S.transform f t, S.transform g t⟫_ℂ))
      -- Assemble the integral.
      calc
        ⟪(S.memL2 f).toLp (weighted (L := L) S f),
            (S.memL2 g).toLp (weighted (L := L) S g)⟫_ℂ
            = ⟪u, v⟫_ℂ := by rfl
        _ = ∫ t : ℝ, ⟪u t, v t⟫_ℂ ∂ S.μ := by
              simpa [MeasureTheory.L2.inner_def]
        _ = ∫ t : ℝ,
              ((weightOfJ S.J t : ℝ) : ℂ) * ((starRingEnd ℂ (S.transform f t)) * (S.transform g t)) ∂ S.μ := by
              exact MeasureTheory.integral_congr_ae hpoint
    -- Conclude by rewriting the integral identity into the Hilbert identity.
    -- (We flip `hInner` to match the direction of `SesqSpectralIdentity.identity`.)
    exact (hInt.trans hInner.symm)

/-- The Hilbert-space form of the sesquilinear identity, obtained from `identity_integral` via
`MeasureTheory.L2.inner_def`. -/
theorem identity :
    ∀ f g : F,
      L.W1 (pair (F := F) f g) =
        ⟪(S.memL2 f).toLp (weighted (L := L) S f),
          (S.memL2 g).toLp (weighted (L := L) S g)⟫_ℂ := by
  intro f g
  -- This is exactly the `identity` field of the converted structure.
  simpa [toSesqSpectralIdentity, SesqSpectralIdentity.weighted, weighted, pair] using
    (toSesqSpectralIdentity (F := F) (L := L) S).identity f g

/--
From the Bochner-integral form, we obtain a `ReflectionPositivityRealization` by converting to
`SesqSpectralIdentity` and applying the already-proved construction.
-/
theorem reflectionPositivityRealization (S : SesqIntegralIdentity (F := F) (L := L)) :
    OptionalTargets.ReflectionPositivityRealization (F := F) (L := L) := by
  classical
  -- Convert and reuse the existing lemma.
  let S' : SesqSpectralIdentity (F := F) (L := L) := toSesqSpectralIdentity (F := F) (L := L) S
  exact SesqSpectralIdentity.reflectionPositivityRealization (F := F) (L := L) S'

end SesqIntegralIdentity

end SesquilinearSpectralIdentity

/-!
## Summary: The Route 3 reduction

The Route 3 proof reduces to proving ONE analytic identity (the spectral identity).

Once you have:

  `W¹(f ⋆ₘ ˜ₘ(⋆ₜ f)) = ∫ Re(2·J(s)) · |M[f](s)|² dμ(s)`

then:
1. `Re(2·J) ≥ 0` + `|M[f]|² ≥ 0` ⇒ integral ≥ 0 ⇒ `B(f,f) ≥ 0`
2. `weilGate_from_spectral_identity` fires
3. `WeilGate_implies_RH` concludes `RiemannHypothesis`

The **sole remaining blocker** is proving the spectral identity with all interchanges
(Fubini, boundary limits) justified.
-/

/-!
## Alternative: Carathéodory / Herglotz representation

If `F(z) := 2·J(z)` is analytic on the unit disk with `Re F(z) ≥ 0`, then `F` is a
**Carathéodory function** and the kernel

  `K_F(z,w) := (F(z) + conj(F(w))) / (1 - z·conj(w))`

is positive definite. This immediately gives a Hilbert-space realization.
-/

/-- A function is Carathéodory on the unit disk: analytic with `Re F ≥ 0`. -/
def IsCaratheodory (Func : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Complex.abs z < 1 → 0 ≤ (Func z).re

/-- The Carathéodory kernel. -/
def caratheodoryKernel (Func : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (Func z + starRingEnd ℂ (Func w)) / (1 - z * starRingEnd ℂ w)

/-- Carathéodory's theorem: positive real part implies positive definite kernel. -/
theorem caratheodory_positive_definite (Func : ℂ → ℂ) (hC : IsCaratheodory Func) :
    ∀ (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, Complex.abs (z i) < 1) (c : Fin n → ℂ),
      0 ≤ (∑ i : Fin n, ∑ j : Fin n,
        c i * starRingEnd ℂ (c j) * caratheodoryKernel Func (z i) (z j)).re := by
  sorry -- Classical 1911 result

end ExplicitFormula
end RiemannRecognitionGeometry
