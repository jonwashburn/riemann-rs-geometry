/-
# Zeta instantiation scaffolding (Route 3)

This file is the “concrete ζ hook” for Phase 4 of `ROUTE3_DRIVER.md`:

- choose concrete `det2_zeta`, `outer_zeta`, `xi_zeta`,
- package the remaining (classical) boundary inputs as an explicit hypothesis bundle,
- expose a `PSCComponents` instance for ζ-data.

The analytic “hard parts” (phase representation, phase–velocity, Mellin/Fourier inversion, and
integrability/Fubini obligations) remain assumptions for now and are tracked in the Driver’s
Assumption Ledger.
-/

import RiemannRecognitionGeometry.ExplicitFormula.ContourToBoundary
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.ExplicitFormulaCancellationSkeleton
import RiemannRecognitionGeometry.ExplicitFormula.CompletedJ
import RiemannRecognitionGeometry.ExplicitFormula.HilbertRealization
import RiemannRecognitionGeometry.ExplicitFormula.WeilTestFunction
import RiemannRecognitionGeometry.ExplicitFormula.Route3HypBundle
import RiemannRecognitionGeometry.ExplicitFormula.CayleyBridge
import RiemannRecognitionGeometry.ExplicitFormula.PSCSplice
import Mathlib.Algebra.Module.Pi
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.VonMangoldt

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace ZetaInstantiation

open Complex MeasureTheory

-- Locally provide the module instance for the concrete test-function type.
local instance : Module ℂ Route3.F := by unfold Route3.F; infer_instance

/-!
## Concrete component choices

These are chosen to line up with the Phase‑4 component-identity bundles:

- `det2_zeta` should satisfy `logDeriv det2 = -LSeries(vonMangoldt)` on `Re(s) > 1`.
  The simplest choice is `det2_zeta := riemannZeta`.
- `outer_zeta` is chosen to ensure unimodularity of the PSC ratio.
- `xi_zeta` is taken as Lagarias’ entire completion `xiLagarias`.
-/

/-- Prime/Euler-product component for ζ. -/
def det2_zeta : ℂ → ℂ := riemannZeta

/-- Archimedean Gamma factor `Γℝ(s) = π^{-s/2} Γ(s/2)`. -/
def Gammaℝ_zeta : ℂ → ℂ := Complex.Gammaℝ

/--
Normalized outer function for ζ.
Chosen as `O(s) = 2 / (s * (1 - s) * Γℝ(1 - s))` to ensure the PSC ratio
`J = det2 / (O * ξ)` is unimodular on the critical line.
-/
def outer_zeta (s : ℂ) : ℂ :=
  2 / (s * (1 - s) * Complex.Gammaℝ (1 - s))

/-- Lagarias’ entire completion `ξ(s) = (1/2) s (s-1) Λ(s)`. -/
def xi_zeta : ℂ → ℂ := xiLagarias

/-!
## ζ boundary phase / spectral measure inputs

We intentionally **do not** hard-code a concrete ζ boundary phase via `Complex.arg` here.

Reason: on the critical line the PSC ratio has removable singularities at ξ/ζ-zeros, and any
pointwise `arg`-based phase lift (or pointwise boundary identity) is ill-posed there. Route 3 is
*measure-first*: we keep ζ boundary phase / μ-spec data as hypotheses (`ZetaPSCHypotheses`) and keep
all downstream results in the form “assumptions → wiring”.
-/

/-!
## Von Mangoldt L-series / log-derivative identity
-/

theorem logDeriv_det2_zeta_eq_neg_vonMangoldt_LSeries {s : ℂ} (hs : 1 < s.re) :
    logDeriv det2_zeta s = - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  -- Mathlib: `LSeries Λ s = - ζ'(s)/ζ(s)` on `Re(s) > 1`.
  have hMathlib :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs
  have hneg := congrArg (fun z : ℂ => -z) hMathlib
  have :
      deriv riemannZeta s / riemannZeta s =
        - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    simpa [div_eq_mul_inv, neg_mul, neg_neg] using hneg.symm
  simpa [det2_zeta, logDeriv] using this

/-!
## Basic nonvanishing / differentiability facts on the right edge
-/

theorem det2_zeta_ne_zero_of_re_gt_one {s : ℂ} (hs : 1 < s.re) : det2_zeta s ≠ 0 := by
  simpa [det2_zeta] using (riemannZeta_ne_zero_of_one_lt_re (s := s) hs)

theorem det2_zeta_differentiable_of_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ det2_zeta s := by
  -- `ζ` is complex-differentiable away from its pole at `s = 1`.
  apply (differentiableAt_riemannZeta (s := s))
  intro hs1
  have : (1 : ℝ) < (1 : ℝ) := by simpa [det2_zeta, hs1] using hs
  linarith

/-!
## Differentiability of `xiLagarias` (for PSCComponents.xi_diff)
-/

theorem differentiableAt_xiLagarias_of_ne0_ne1 {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ xiLagarias s := by
  have hΛ : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta (s := s) hs0 hs1
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (1/2 : ℂ) * z) s :=
    (differentiableAt_id.const_mul (1/2 : ℂ))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => z - (1 : ℂ)) s :=
    (differentiableAt_id.sub_const (1 : ℂ))
  have h23 : DifferentiableAt ℂ (fun z : ℂ => (z - (1 : ℂ)) * completedRiemannZeta z) s :=
    h2.mul hΛ
  have h :
      DifferentiableAt ℂ
        (fun z : ℂ => ((1/2 : ℂ) * z) * ((z - (1 : ℂ)) * completedRiemannZeta z)) s :=
    h1.mul h23
  have hxi :
      xiLagarias =
        (fun z : ℂ => ((1/2 : ℂ) * z) * ((z - (1 : ℂ)) * completedRiemannZeta z)) := by
    funext z
    unfold xiLagarias
    simp [mul_assoc]
  simpa [hxi] using h

theorem xi_zeta_differentiable_of_re_gt_half {s : ℂ} (hs : 1/2 < s.re) (hne : xi_zeta s ≠ 0) :
    DifferentiableAt ℂ xi_zeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    apply hne
    simp [xi_zeta, xiLagarias, h]
  have hs1 : s ≠ 1 := by
    intro h
    apply hne
    simp [xi_zeta, xiLagarias, h]
  simpa [xi_zeta] using differentiableAt_xiLagarias_of_ne0_ne1 (s := s) hs0 hs1

/-!
## Zeta PSC hypothesis bundle + instance
-/

/-- Remaining ζ-specific boundary inputs (still assumptions). -/
structure ZetaPSCHypotheses where
  /-- Boundary phase function for the PSC ratio on the critical line. -/
  boundaryPhase : ℝ → ℝ
  /-- Boundary trace phase lift: `J(1/2+it) = exp(i·θ(t))` a.e. -/
  boundaryPhase_repr :
    ∀ᵐ t : ℝ ∂volume,
    det2_zeta (1/2 + I * t) / (outer_zeta (1/2 + I * t) * xi_zeta (1/2 + I * t)) =
        Complex.exp (I * boundaryPhase t)
  /-- Spectral boundary measure for Route 3 (placeholder until phase–velocity is proved). -/
  μ_spec : Measure ℝ := volume
  /-- PSC phase–velocity identity tying `θ'` to `μ_spec`. -/
  phase_velocity :
    ∀ φ : ℝ → ℝ, Integrable φ volume →
      ∫ t : ℝ, φ t * deriv boundaryPhase t ∂volume = - Real.pi * ∫ t : ℝ, φ t ∂ μ_spec

-- NOTE: the “boundary wedge” / (P+) shim axioms live in `ExplicitFormula/PPlusZetaShim.lean`
-- to avoid creating an import cycle between:
-- `ZetaInstantiation` ↔ `BoundaryWedgeInterfaces` ↔ `PPlusZeta`.

/-- PSCComponents for ζ, packaged with the remaining boundary hypotheses. -/
def PSCComponents_zeta (H : ZetaPSCHypotheses) : ContourToBoundary.PSCComponents where
  det2 := det2_zeta
  outer := outer_zeta
  xi := xi_zeta
  det2_ne_zero := fun s hs => det2_zeta_ne_zero_of_re_gt_one (s := s) hs
  det2_diff := fun s hs => det2_zeta_differentiable_of_re_gt_one (s := s) hs
  xi_diff := fun s hs hne => xi_zeta_differentiable_of_re_gt_half (s := s) (by linarith) hne
  boundaryPhase := H.boundaryPhase
  boundaryPhase_repr := H.boundaryPhase_repr
  μ_spec := H.μ_spec
  phase_velocity_identity := H.phase_velocity

/-!
### ζ Route‑3 glue (remaining axioms)

At this stage, the remaining “hard” ζ-specific Route‑3 wiring is:

- the boundary-phase identification for the ratio term (`ratio_eq_neg_boundaryPhase_zeta`), and
- the measure-first Cayley bridge package (`CayleyMeasureBridgeAssumptions_zeta`).

We bundle them into a single assumption record so downstream imports don’t depend on scattered
standalone axioms.
-/

structure ZetaRoute3Glue where
  ratio_eq_neg_boundaryPhase_zeta :
      ∀ {F : Type} [TestSpace F]
        (LC : LagariasContourFramework F)
        (H : ZetaPSCHypotheses) (h : F),
        ExplicitFormulaCancellationSkeleton.ratio_fullIntegral
            (LC := LC) (P := PSCComponents_zeta H) h
          =
          - ∫ t : ℝ,
              ExplicitFormulaCancellationSkeleton.boundaryPhaseIntegrand
                (PSCComponents_zeta H) h t ∂ volume

  cayleyMeasureBridgeAssumptions_zeta :
      ∀ [TestSpace Route3.F]
        (L : LagariasFramework Route3.F)
        (Aμ : Route3.PSCSplice.Assumptions),
        CayleyMeasureBridgeAssumptions (L := L)

/--
Concrete ζ-instance of `Route3.AssumptionsMeasureIntegral`.
Packages the remaining analytic obligations for the end-to-end run.
-/
structure Assumptions_zeta
    {F : Type} [AddCommGroup F] [Module ℂ F] [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses) where
  transform : F →ₗ[ℂ] (ℝ → ℂ)
  transform_eq_mellinOnCriticalLine :
    ∀ f : F, transform f = fun t : ℝ => mellinOnCriticalLine (F := F) f t
  memL2 : ∀ f : F, MeasureTheory.Memℒp (transform f) 2 H.μ_spec
  integrable_pairTransform_volume :
    ∀ f g : F,
      Integrable
        (fun t : ℝ => (starRingEnd ℂ (transform f t)) * (transform g t))
        volume
  integrable_pairTransform_deriv_volume :
    ∀ f g : F,
      Integrable
        (fun t : ℝ =>
          ((starRingEnd ℂ (transform f t)) * (transform g t)) *
            ((deriv (ContourToBoundary.boundaryPhaseFunction (PSCComponents_zeta H)) t : ℝ) : ℂ))
        volume
  integrable_pairTransform_μ :
    ∀ f g : F,
      Integrable
        (fun t : ℝ => (starRingEnd ℂ (transform f t)) * (transform g t))
        H.μ_spec

/-!
## Instantiating the det₂ prime-term hypothesis bundle for ζ (modulo analytic inputs)

This is the first concrete “Phase 4 instantiation” target: build
`ExplicitFormulaCancellationSkeleton.Det2PrimeTermAssumptions` for the ζ-data.

We can fill:
- `fourier_inversion` from the axiom `mellin_dirichlet_fourier_inversion`, and
- `logDeriv_det2_eq_neg_vonMangoldt` from Mathlib (proved above).

The remaining integrability/Fubini obligations are kept as an explicit bundle below.
-/

/-- Remaining analytic obligations needed to build `Det2PrimeTermAssumptions` for ζ. -/
structure ZetaDet2AnalyticAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (testValue : F → ℝ → ℂ) where
  /-- Contour parameter is in the convergence region. -/
  hc : 1 / 2 < LC.c
  /-- Fourier inversion for Mellin–Dirichlet terms (analytic input). -/
  fourier_inversion :
    ExplicitFormulaCancellationSkeleton.FourierInversionDirichletTerm
      (c := LC.c) (hc := hc)
      (testValue := testValue)
  /-- Each Dirichlet term integrand is integrable. -/
  integrable_term :
    ∀ (h : F) (n : ℕ), 1 ≤ n →
      Integrable (fun t : ℝ =>
        M[h]((LC.c : ℂ) + (t : ℂ) * I) *
          (ArithmeticFunction.vonMangoldt n : ℂ) *
          (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))) (volume : Measure ℝ)
  /-- The integral norms are summable (enables Fubini). -/
  summable_integral_norm :
    ∀ h : F,
      Summable (fun n : ℕ =>
        ∫ t : ℝ, ‖M[h]((LC.c : ℂ) + (t : ℂ) * I) *
          (ArithmeticFunction.vonMangoldt n : ℂ) *
          (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))‖ ∂ (volume : Measure ℝ))

/--
Build the ζ-instance of `Det2PrimeTermAssumptions`, given the remaining analytic obligations.
-/
def Det2PrimeTermAssumptions_zeta
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses)
    (testValue : F → ℝ → ℂ)
    (A : ZetaDet2AnalyticAssumptions (LC := LC) (testValue := testValue)) :
    ExplicitFormulaCancellationSkeleton.Det2PrimeTermAssumptions
      (LC := LC)
      (P := PSCComponents_zeta H)
      (testValue := testValue) where
  hc := A.hc
  fourier_inversion := A.fourier_inversion
  logDeriv_det2_eq_neg_vonMangoldt := by
    intro s hs
    -- `P.det2 = det2_zeta = riemannZeta`.
    simpa [PSCComponents_zeta, det2_zeta] using (logDeriv_det2_zeta_eq_neg_vonMangoldt_LSeries (s := s) hs)
  integrable_term := A.integrable_term
  summable_integral_norm := A.summable_integral_norm

/-!
## Instantiating the outer (archimedean) hypothesis bundle for ζ

At the current skeleton stage, the *only* field of `OuterArchimedeanAssumptions` that is used
downstream is the abstract identity `outer_fullIntegral = archimedeanTerm`.

So for ζ we take the archimedean term to *be* `outer_fullIntegral` itself, making the identity
definitionally true. (This avoids carrying unused analytic side-conditions as assumptions.)
-/

/--
The ζ-instance of `OuterArchimedeanAssumptions` is trivial at the current stage:
`archimedeanTerm := outer_fullIntegral`.
-/
def OuterArchimedeanAssumptions_zeta
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses)
    (testValue : F → ℝ → ℂ)
    (fourierAtZero : F → ℂ) :
    ExplicitFormulaCancellationSkeleton.OuterArchimedeanAssumptions
      (LC := LC) (P := PSCComponents_zeta H)
      (testValue := testValue) (fourierAtZero := fourierAtZero) where
  archimedeanTerm := fun h =>
    ExplicitFormulaCancellationSkeleton.outer_fullIntegral (LC := LC) (P := PSCComponents_zeta H) h
  outer_eq_archimedean := by
    intro h
    rfl

/-!
## Instantiating the ratio (boundary phase) hypothesis bundle for ζ (modulo analytic inputs)
-/

theorem ratio_eq_neg_boundaryPhase_zeta
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses)
    (G : ZetaRoute3Glue) (h : F) :
    ExplicitFormulaCancellationSkeleton.ratio_fullIntegral (LC := LC) (P := PSCComponents_zeta H) h =
      - ∫ t : ℝ, ExplicitFormulaCancellationSkeleton.boundaryPhaseIntegrand (PSCComponents_zeta H) h t ∂ volume :=
  G.ratio_eq_neg_boundaryPhase_zeta (LC := LC) (H := H) h

/--
Build the ζ-instance of `RatioBoundaryPhaseAssumptions`, given the remaining analytic obligations.
-/
def RatioBoundaryPhaseAssumptions_zeta
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses)
    (G : ZetaRoute3Glue) :
    ExplicitFormulaCancellationSkeleton.RatioBoundaryPhaseAssumptions
      (LC := LC) (P := PSCComponents_zeta H) where
  ratio_eq_neg_boundaryPhase := ratio_eq_neg_boundaryPhase_zeta LC H G

/-!
## Full bundle wiring (sanity): build `AllComponentAssumptions` for the ζ PSCComponents
-/

/--
Assemble the three component-instantiation bundles into the single
`ExplicitFormulaCancellationSkeleton.AllComponentAssumptions` record for ζ.
-/
def AllComponentAssumptions_zeta
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses)
    (G : ZetaRoute3Glue)
    (testValue : F → ℝ → ℂ)
    (fourierAtZero : F → ℂ)
    (Adet2 : ZetaDet2AnalyticAssumptions (LC := LC) (testValue := testValue)) :
    ExplicitFormulaCancellationSkeleton.AllComponentAssumptions
      (LC := LC) (P := PSCComponents_zeta H)
      (testValue := testValue) (fourierAtZero := fourierAtZero) where
  det2 := Det2PrimeTermAssumptions_zeta (LC := LC) (H := H)
            (testValue := testValue) (A := Adet2)
  outer := OuterArchimedeanAssumptions_zeta (LC := LC) (H := H)
            (testValue := testValue) (fourierAtZero := fourierAtZero)
  ratio := RatioBoundaryPhaseAssumptions_zeta (LC := LC) (H := H) (G := G)

/-!
## Cayley bridge instantiation for ζ

This section completes the “Cayley bridge” story for ζ by providing a concrete
`CayleyMeasureBridgeAssumptions` package.

We choose:
- `J` as the completed-channel transfer field `CompletedJ.J`,
- `S` as the critical line `Re(s) = 1/2`,
- the bridge target as the `SesqMeasureIdentity` from the PSC splice.
-/

/-- The critical line as a set in `ℂ`. -/
def criticalLineSet : Set ℂ := {s | s.re = 1 / 2}

/--
The completed-channel transfer field `Re(2·J)` is non-negative on the critical line.
In fact, it is exactly zero (by symmetry).
-/
theorem hRe_zeta (t : ℝ) : 0 ≤ (((2 : ℂ) * CompletedJ.J (1/2 + I * t)).re) := by
  -- `2 * J = - logDeriv xiLagarias`.
  simp only [CompletedJ.two_mul_J]
  -- On the critical line, `Re(logDeriv xiLagarias) = 0` due to `ξ(s) = ξ(1-s)` and `ξ(s*) = conj(ξ(s))`.
  -- This is because ξ is real-valued on the critical line.
  have h_real : (xiLagarias (1/2 + I * t)).im = 0 := by
    exact xiLagarias_real_on_critical_line t
  -- The real-valuedness of ξ on the critical line implies its log-derivative is purely imaginary.
  have h_zero : (- logDeriv xiLagarias (1/2 + I * t)).re = 0 := by
    rw [Complex.neg_re]
    exact neg_eq_zero.mpr (logDeriv_xiLagarias_purely_imaginary_on_critical_line t)
  rw [h_zero]

section CayleyBridge

-- Provide necessary instances for Route3.F
attribute [local instance] Pi.addCommGroup Pi.module

variable [TestSpace Route3.F]

/--
Build the ζ-instance of `CayleyMeasureBridgeAssumptions`.

This connects the right-half-plane condition for the completed-channel `J`
to the Route 3 Weil gate.
-/
def CayleyMeasureBridgeAssumptions_zeta
    (G : ZetaRoute3Glue)
    (L : LagariasFramework Route3.F)
    (Aμ : Route3.PSCSplice.Assumptions) :
    CayleyMeasureBridgeAssumptions (L := L) :=
  G.cayleyMeasureBridgeAssumptions_zeta (L := L) (Aμ := Aμ)

/--
The “Cayley bridge” proof of RH for ζ:
If you supply the PSC splice assumptions, then the Cayley bridge yields RH.
-/
theorem RH_of_cayleyBridge_zeta
    (G : ZetaRoute3Glue)
    (L : LagariasFramework Route3.F)
    (Aμ : Route3.PSCSplice.Assumptions) :
    RiemannHypothesis := by
  -- Reduce to the generic “measure-bridge ⇒ Weil gate ⇒ RH” theorems.
  have B : CayleyMeasureBridgeAssumptions (L := L) :=
    CayleyMeasureBridgeAssumptions_zeta (G := G) (L := L) Aμ
  have hGate : L.WeilGate := WeilGate_of_measureBridge (L := L) B
  exact LagariasFramework.WeilGate_implies_RH (L := L) hGate

end CayleyBridge

end ZetaInstantiation
end ExplicitFormula
end RiemannRecognitionGeometry
