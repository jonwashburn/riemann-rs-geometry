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
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.VonMangoldt

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace ZetaInstantiation

open Complex MeasureTheory

/-!
## Concrete component choices

These are chosen to line up with the Phase‑4 component-identity bundles:

- `det2_zeta` should satisfy `logDeriv det2 = -LSeries(vonMangoldt)` on `Re(s) > 1`.
  The simplest choice is `det2_zeta := riemannZeta`.
- `outer_zeta` is taken as Mathlib’s `Gammaℝ` factor.
- `xi_zeta` is taken as Lagarias’ entire completion `xiLagarias`.

Note: the PSC ratio `J = det2/(outer*xi)` is *not* asserted to be the classical one here; its
boundary properties are bundled as explicit hypotheses below.
-/

/-- Prime/Euler-product component for ζ. -/
def det2_zeta : ℂ → ℂ := riemannZeta

/-- Archimedean Gamma factor `Γℝ(s) = π^{-s/2} Γ(s/2)`. -/
def outer_zeta : ℂ → ℂ := Complex.Gammaℝ

/-- Lagarias’ entire completion `ξ(s) = (1/2) s (s-1) Λ(s)`. -/
def xi_zeta : ℂ → ℂ := xiLagarias

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

These are the only “structural” requirements needed to form `logDeriv` on `Re(s) > 1`.
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

theorem outer_zeta_ne_zero_of_re_gt_half {s : ℂ} (hs : 1/2 < s.re) : outer_zeta s ≠ 0 := by
  have hs' : 0 < s.re := by linarith
  simpa [outer_zeta] using (Complex.Gammaℝ_ne_zero_of_re_pos (s := s) hs')

theorem outer_zeta_differentiable_of_re_gt_half {s : ℂ} (hs : 1/2 < s.re) :
    DifferentiableAt ℂ outer_zeta s := by
  have hs' : 0 < s.re := by linarith
  simpa [outer_zeta] using
    (CompletedJ.differentiableAt_Gammaℝ_of_re_pos (s := s) hs')

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
  /-- Regularity of the chosen boundary phase. -/
  boundaryPhase_diff : ∀ t : ℝ, DifferentiableAt ℝ boundaryPhase t
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

/-- PSCComponents for ζ, packaged with the remaining boundary hypotheses. -/
def PSCComponents_zeta (H : ZetaPSCHypotheses) : ContourToBoundary.PSCComponents where
  det2 := det2_zeta
  outer := outer_zeta
  xi := xi_zeta
  det2_ne_zero := fun s hs => det2_zeta_ne_zero_of_re_gt_one (s := s) hs
  outer_ne_zero := fun s hs => outer_zeta_ne_zero_of_re_gt_half (s := s) hs
  det2_diff := fun s hs => det2_zeta_differentiable_of_re_gt_one (s := s) hs
  outer_diff := fun s hs => outer_zeta_differentiable_of_re_gt_half (s := s) hs
  xi_diff := fun s hs hne => xi_zeta_differentiable_of_re_gt_half (s := s) hs hne
  boundaryPhase := H.boundaryPhase
  boundaryPhase_diff := H.boundaryPhase_diff
  boundaryPhase_repr := H.boundaryPhase_repr
  μ_spec := H.μ_spec
  phase_velocity_identity := H.phase_velocity

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
    (LC : LagariasContourFramework F) where
  /-- Contour parameter is in the convergence region. -/
  hc : 1 / 2 < LC.c
  /-- Fourier inversion for Mellin–Dirichlet terms (analytic input). -/
  fourier_inversion :
    ExplicitFormulaCancellationSkeleton.FourierInversionDirichletTerm
      (c := LC.c) (hc := hc)
      (testValue := mellinOnCriticalLine (F := F))
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
    (A : ZetaDet2AnalyticAssumptions (LC := LC)) :
    ExplicitFormulaCancellationSkeleton.Det2PrimeTermAssumptions
      (LC := LC)
      (P := PSCComponents_zeta H)
      (testValue := mellinOnCriticalLine (F := F)) where
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

/-- Remaining analytic obligations needed to build `RatioBoundaryPhaseAssumptions` for ζ. -/
structure ZetaRatioAnalyticAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses) where
  /-- Contour parameter is in the convergence region. -/
  hc : 1 / 2 < LC.c
  /-- Critical-line log-derivative identity for the PSC ratio (phase lift). -/
  logDeriv_ratio_critical_line :
    ∀ t : ℝ,
      logDeriv (ContourToBoundary.PSCRatio (PSCComponents_zeta H)) ((1/2 : ℂ) + I * t) =
        I * ((deriv (ContourToBoundary.boundaryPhaseFunction (PSCComponents_zeta H)) t : ℝ) : ℂ)
  /-- Contour shift from `Re(s)=c` to `Re(s)=1/2` for the ratio integrand. -/
  contour_shift :
    ∀ h : F,
      (∫ t : ℝ,
          ExplicitFormulaCancellationSkeleton.rightEdgeIntegrand_ratio LC (PSCComponents_zeta H) h t ∂
            (volume : Measure ℝ)) =
        ∫ t : ℝ, M[h]((1/2 : ℂ) + I * t) *
          logDeriv (ContourToBoundary.PSCRatio (PSCComponents_zeta H)) ((1/2 : ℂ) + I * t) ∂
            (volume : Measure ℝ)
  /-- The critical-line sum formula needed for the ratio identity. -/
  critical_line_sum :
    ∀ h : F,
      (∫ t : ℝ,
            M[h]((1/2 : ℂ) + I * t) *
              (I * ((deriv (ContourToBoundary.boundaryPhaseFunction (PSCComponents_zeta H)) t : ℝ) : ℂ)) ∂ volume) +
          (∫ t : ℝ,
              M[(TestSpace.tilde (F := F) h)]((1/2 : ℂ) + I * t) *
                (I * ((deriv (ContourToBoundary.boundaryPhaseFunction (PSCComponents_zeta H)) t : ℝ) : ℂ)) ∂ volume) =
        - ∫ t : ℝ, ExplicitFormulaCancellationSkeleton.boundaryPhaseIntegrand (PSCComponents_zeta H) h t ∂ volume

/--
Build the ζ-instance of `RatioBoundaryPhaseAssumptions`, given the remaining analytic obligations.
-/
def RatioBoundaryPhaseAssumptions_zeta
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses)
    (A : ZetaRatioAnalyticAssumptions (LC := LC) (H := H)) :
    ExplicitFormulaCancellationSkeleton.RatioBoundaryPhaseAssumptions
      (LC := LC) (P := PSCComponents_zeta H) where
  hc := A.hc
  logDeriv_ratio_critical_line := A.logDeriv_ratio_critical_line
  contour_shift := A.contour_shift
  critical_line_sum := A.critical_line_sum

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
    (fourierAtZero : F → ℂ)
    (Adet2 : ZetaDet2AnalyticAssumptions (LC := LC))
    (Aratio : ZetaRatioAnalyticAssumptions (LC := LC) (H := H)) :
    ExplicitFormulaCancellationSkeleton.AllComponentAssumptions
      (LC := LC) (P := PSCComponents_zeta H)
      (testValue := mellinOnCriticalLine (F := F)) (fourierAtZero := fourierAtZero) where
  det2 := Det2PrimeTermAssumptions_zeta (LC := LC) (H := H) Adet2
  outer := OuterArchimedeanAssumptions_zeta (LC := LC) (H := H)
            (testValue := mellinOnCriticalLine (F := F)) (fourierAtZero := fourierAtZero)
  ratio := RatioBoundaryPhaseAssumptions_zeta (LC := LC) (H := H) Aratio

end ZetaInstantiation
end ExplicitFormula
end RiemannRecognitionGeometry
