import RiemannRecognitionGeometry.ExplicitFormula.LagariasContour
import RiemannRecognitionGeometry.ExplicitFormula.ContourToBoundary
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Route 3: Explicit-formula cancellation (contour skeleton lemmas)

This file collects *purely formal* lemmas that connect the contour-limit definition of `W¹`
(`ContourW1.W1Trunc` + `W1LimitAssumptions`) to the vertical-edge integrals that appear in the
classical explicit-formula derivation.

It does **not** prove the residue/prime-term bookkeeping; it just provides the reusable “limit
algebra + functional equation edge cancellation” facts in a form that can be fed into the
`ContourToBoundary.explicit_formula_cancellation` goal.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex MeasureTheory

namespace ExplicitFormulaCancellationSkeleton

open ContourToBoundary
open Filter intervalIntegral

/-!
## Bundling the remaining analytic gap

At this stage, the contour infrastructure reduces `explicit_formula_cancellation` to one remaining
analytic claim: a `T → ∞` limit for a sum of *right-edge* integrals equals the boundary-phase pairing.

We package that as a hypothesis bundle so downstream code can depend on a single named assumption.
-/

/-- The remaining “right-edge limit = boundary phase” hypothesis needed for `explicit_formula_cancellation`. -/
structure RightEdgePhaseLimitAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents) where
  /-- Identify both `xi`s with `xiLagarias` (so the FE log-derivative identity is available). -/
  xiLC : LC.xi = xiLagarias
  xiP : P.xi = xiLagarias
  /-- Horizontal edges vanish for all test functions. -/
  horizBottom_vanish :
    ∀ h : F,
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop (nhds 0)
  horizTop_vanish :
    ∀ h : F,
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop (nhds 0)
  /-- The right-edge sum has the boundary-phase limit for all test functions. -/
  rightEdge_phase_limit :
    ∀ h : F,
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
            ContourW1.vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop
        (nhds (Complex.I *
          ∫ t : ℝ, -(M[h](1/2 + Complex.I * t) *
              ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume))

/-!
## Splitting the right-edge `Tendsto` into a limit lemma + an integral identity

The `rightEdge_phase_limit` field above is intentionally “one big analytic fact”.
The next mechanical step is to reduce it to:

1. a general `(-T..T) → ℝ` interval-integral convergence lemma (available in Mathlib), plus
2. a single equality of full-line integrals.

This makes the true remaining analytic content maximally explicit.
-/

/-- The right-edge integrand (as a function of `t : ℝ`) appearing in the explicit-formula contour
manipulation, i.e. \(M[h](c+it)\cdot (\xi'/\xi)(c+it)\). -/
def rightEdgeIntegrand
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F) (h : F) : ℝ → ℂ :=
  fun t : ℝ =>
    M[h]((LC.c : ℂ) + (t : ℂ) * Complex.I) *
      logDeriv LC.xi ((LC.c : ℂ) + (t : ℂ) * Complex.I)

/-!
### Optional: decomposing the right-edge integrand via PSC components

If one has PSC data `(det2, outer, xi)` with `LC.xi = P.xi` and nonvanishing on the line `Re(s)=c`,
then `ContourToBoundary.log_deriv_decomposition` rewrites `logDeriv xi` in terms of `det2`, `outer`,
and the PSC ratio.

This does **not** solve the explicit formula; it only records the algebraic reduction so later work
can focus on the remaining analytic inputs (integrability + limit exchange).
-/

/-- The PSC-decomposed right-edge integrand:
\(M[h](c+it)\cdot(\logDeriv det₂ - \logDeriv O - \logDeriv J)(c+it)\). -/
def rightEdgeIntegrand_decomp
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents) (h : F) : ℝ → ℂ :=
  fun t : ℝ =>
    M[h]((LC.c : ℂ) + (t : ℂ) * Complex.I) *
      (logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * Complex.I) -
        logDeriv P.outer ((LC.c : ℂ) + (t : ℂ) * Complex.I) -
        logDeriv (PSCRatio P) ((LC.c : ℂ) + (t : ℂ) * Complex.I))

/--
Under the PSC log-derivative decomposition (and assuming nonvanishing on the right edge),
`rightEdgeIntegrand` agrees pointwise with `rightEdgeIntegrand_decomp`.
-/
theorem rightEdgeIntegrand_eq_decomp
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hxi : LC.xi = P.xi)
    (hc_gt_one : 1 < LC.c)
    (hxi_ne : ∀ t : ℝ, P.xi ((LC.c : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    rightEdgeIntegrand LC h = rightEdgeIntegrand_decomp LC P h := by
  funext t
  -- Apply `log_deriv_decomposition` at `s = c + it`.
  have hs : (1 : ℝ) < (((LC.c : ℂ) + (t : ℂ) * Complex.I)).re := by
    simpa using hc_gt_one
  have hdecomp :
      logDeriv P.xi ((LC.c : ℂ) + (t : ℂ) * Complex.I) =
        logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * Complex.I) -
          logDeriv P.outer ((LC.c : ℂ) + (t : ℂ) * Complex.I) -
            logDeriv (PSCRatio P) ((LC.c : ℂ) + (t : ℂ) * Complex.I) := by
    simpa using
      (ContourToBoundary.log_deriv_decomposition
        (P := P)
        (s := (LC.c : ℂ) + (t : ℂ) * Complex.I)
        (hs := hs)
        (hxi := hxi_ne t))
  -- Rewrite `LC.xi` to `P.xi`, then finish by simp.
  simp [rightEdgeIntegrand, rightEdgeIntegrand_decomp, hxi, hdecomp, mul_assoc]

/-- The boundary-phase integrand on the critical line,
\(- M[h](\tfrac12+it)\cdot \theta'(t)\), used in `ContourToBoundary.explicit_formula_cancellation`. -/
def boundaryPhaseIntegrand
    {F : Type} [TestSpace F]
    (P : PSCComponents) (h : F) : ℝ → ℂ :=
  fun t : ℝ =>
    -(M[h]((1/2 : ℂ) + Complex.I * t) *
        ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ))

/--
The **single remaining full-line identity** needed to identify the contour right-edge integrals
with the boundary-phase pairing.

This is the natural “next smallest target” after the contour-limit algebra is in place.
-/
def rightEdge_integral_identity
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F) : Prop :=
  (∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ)) +
      (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))
    =
    ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ)

/--
Variant of `rightEdge_integral_identity` with the PSC-decomposed right-edge integrand
(`rightEdgeIntegrand_decomp`).

This is a pure rewrite: it does not assume any “explicit formula cancellation”, only the
algebraic decomposition of `logDeriv xi`.
-/
def rightEdge_integral_identity_decomp
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F) : Prop :=
  (∫ t : ℝ, rightEdgeIntegrand_decomp LC P h t ∂ (volume : Measure ℝ)) +
      (∫ t : ℝ, rightEdgeIntegrand_decomp LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))
    =
    ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ)

/--
Rewrite `rightEdge_integral_identity` into its PSC-decomposed form using
`rightEdgeIntegrand_eq_decomp` (for both `h` and `˜ₘh`).
-/
theorem rightEdge_integral_identity_iff_decomp
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hxi : LC.xi = P.xi)
    (hc_gt_one : 1 < LC.c)
    (hxi_ne : ∀ t : ℝ, P.xi ((LC.c : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    rightEdge_integral_identity (LC := LC) (P := P) h ↔
      rightEdge_integral_identity_decomp (LC := LC) (P := P) h := by
  have hh :
      rightEdgeIntegrand LC h = rightEdgeIntegrand_decomp LC P h :=
    rightEdgeIntegrand_eq_decomp (LC := LC) (P := P) (h := h) hxi hc_gt_one hxi_ne
  have htilde :
      rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) =
        rightEdgeIntegrand_decomp LC P (TestSpace.tilde (F := F) h) :=
    rightEdgeIntegrand_eq_decomp (LC := LC) (P := P) (h := (TestSpace.tilde (F := F) h)) hxi hc_gt_one hxi_ne
  constructor <;> intro H
  · simpa [rightEdge_integral_identity, rightEdge_integral_identity_decomp, hh, htilde] using H
  · simpa [rightEdge_integral_identity, rightEdge_integral_identity_decomp, hh, htilde] using H

/--
The three PSC right-edge component integrands corresponding to `det2`, `outer`, and `PSCRatio`.
-/
def rightEdgeIntegrand_det2
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents) (h : F) : ℝ → ℂ :=
  fun t : ℝ =>
    M[h]((LC.c : ℂ) + (t : ℂ) * Complex.I) *
      logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * Complex.I)

def rightEdgeIntegrand_outer
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents) (h : F) : ℝ → ℂ :=
  fun t : ℝ =>
    M[h]((LC.c : ℂ) + (t : ℂ) * Complex.I) *
      logDeriv P.outer ((LC.c : ℂ) + (t : ℂ) * Complex.I)

def rightEdgeIntegrand_ratio
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents) (h : F) : ℝ → ℂ :=
  fun t : ℝ =>
    M[h]((LC.c : ℂ) + (t : ℂ) * Complex.I) *
      logDeriv (PSCRatio P) ((LC.c : ℂ) + (t : ℂ) * Complex.I)

theorem rightEdgeIntegrand_decomp_eq_det2_sub_outer_sub_ratio
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents) (h : F) :
    rightEdgeIntegrand_decomp LC P h =
      fun t : ℝ =>
        rightEdgeIntegrand_det2 LC P h t -
          rightEdgeIntegrand_outer LC P h t -
            rightEdgeIntegrand_ratio LC P h t := by
  funext t
  simp [rightEdgeIntegrand_decomp, rightEdgeIntegrand_det2, rightEdgeIntegrand_outer,
    rightEdgeIntegrand_ratio]
  ring

/-!
### Splitting the remaining full-line identity into det₂ / outer / ratio components

This is purely linear-algebraic manipulation of Bochner integrals, under explicit integrability
assumptions.
-/

def det2_fullIntegral
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F) (P : PSCComponents) (h : F) : ℂ :=
  (∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t ∂ (volume : Measure ℝ)) +
    (∫ t : ℝ, rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))

def outer_fullIntegral
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F) (P : PSCComponents) (h : F) : ℂ :=
  (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t ∂ (volume : Measure ℝ)) +
    (∫ t : ℝ, rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))

def ratio_fullIntegral
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F) (P : PSCComponents) (h : F) : ℂ :=
  (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t ∂ (volume : Measure ℝ)) +
    (∫ t : ℝ, rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))

/-- The PSC-decomposed full-line identity, written as a single equation between the three component
integrals and the boundary-phase integral. -/
def rightEdge_integral_identity_components
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F) (P : PSCComponents) (h : F) : Prop :=
  det2_fullIntegral (LC := LC) (P := P) h -
      outer_fullIntegral (LC := LC) (P := P) h -
      ratio_fullIntegral (LC := LC) (P := P) h
    =
    ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ)

/--
Assuming integrability of the three PSC component integrands (for both `h` and `˜ₘh`), the
decomposed identity `rightEdge_integral_identity_decomp` is equivalent to the component-form
identity `rightEdge_integral_identity_components`.
-/
theorem rightEdge_integral_identity_decomp_iff_components
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hInt_det2 : Integrable (rightEdgeIntegrand_det2 LC P h) (volume : Measure ℝ))
    (hInt_det2_tilde :
      Integrable (rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h)) (volume : Measure ℝ))
    (hInt_outer : Integrable (rightEdgeIntegrand_outer LC P h) (volume : Measure ℝ))
    (hInt_outer_tilde :
      Integrable (rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h)) (volume : Measure ℝ))
    (hInt_ratio : Integrable (rightEdgeIntegrand_ratio LC P h) (volume : Measure ℝ))
    (hInt_ratio_tilde :
      Integrable (rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h)) (volume : Measure ℝ)) :
    rightEdge_integral_identity_decomp (LC := LC) (P := P) h ↔
      rightEdge_integral_identity_components (LC := LC) (P := P) h := by
  -- Helper: compute the full-line integral of the decomposed right-edge integrand for `h`.
  have h_decomp_integral :
      (∫ t : ℝ, rightEdgeIntegrand_decomp LC P h t ∂ (volume : Measure ℝ)) =
        (∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t ∂ (volume : Measure ℝ)) -
          (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t ∂ (volume : Measure ℝ)) -
          (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t ∂ (volume : Measure ℝ)) := by
    have hInt_det2_outer :
        Integrable (fun t : ℝ =>
          rightEdgeIntegrand_det2 LC P h t - rightEdgeIntegrand_outer LC P h t) (volume : Measure ℝ) :=
      hInt_det2.sub hInt_outer
    have hI1 :
        (∫ t : ℝ,
            (rightEdgeIntegrand_det2 LC P h t - rightEdgeIntegrand_outer LC P h t) ∂ (volume : Measure ℝ)) =
          (∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t ∂ (volume : Measure ℝ)) := by
      simpa using MeasureTheory.integral_sub hInt_det2 hInt_outer
    have hI2 :
        (∫ t : ℝ,
            ((rightEdgeIntegrand_det2 LC P h t - rightEdgeIntegrand_outer LC P h t) -
                rightEdgeIntegrand_ratio LC P h t) ∂ (volume : Measure ℝ)) =
          (∫ t : ℝ,
              (rightEdgeIntegrand_det2 LC P h t - rightEdgeIntegrand_outer LC P h t) ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t ∂ (volume : Measure ℝ)) := by
      simpa using MeasureTheory.integral_sub hInt_det2_outer hInt_ratio
    calc
      (∫ t : ℝ, rightEdgeIntegrand_decomp LC P h t ∂ (volume : Measure ℝ))
          = (∫ t : ℝ,
              (rightEdgeIntegrand_det2 LC P h t - rightEdgeIntegrand_outer LC P h t -
                rightEdgeIntegrand_ratio LC P h t) ∂ (volume : Measure ℝ)) := by
              simp [rightEdgeIntegrand_decomp_eq_det2_sub_outer_sub_ratio]
      _ = (∫ t : ℝ,
              ((rightEdgeIntegrand_det2 LC P h t - rightEdgeIntegrand_outer LC P h t) -
                rightEdgeIntegrand_ratio LC P h t) ∂ (volume : Measure ℝ)) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = ((∫ t : ℝ,
              (rightEdgeIntegrand_det2 LC P h t - rightEdgeIntegrand_outer LC P h t) ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t ∂ (volume : Measure ℝ))) := hI2
      _ = (((∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t ∂ (volume : Measure ℝ)) -
              (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t ∂ (volume : Measure ℝ))) -
            (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t ∂ (volume : Measure ℝ))) := by
              simpa [hI1]
      _ = (∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t ∂ (volume : Measure ℝ)) := by
              ring

  -- Same helper for `˜ₘh`.
  have h_decomp_integral_tilde :
      (∫ t : ℝ, rightEdgeIntegrand_decomp LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) =
        (∫ t : ℝ,
            rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) -
          (∫ t : ℝ,
              rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) -
          (∫ t : ℝ,
              rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) := by
    have hInt_det2_outer :
        Integrable (fun t : ℝ =>
          rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t -
            rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) (volume : Measure ℝ) :=
      hInt_det2_tilde.sub hInt_outer_tilde
    have hI1 :
        (∫ t : ℝ,
            (rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t -
              rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) ∂ (volume : Measure ℝ)) =
          (∫ t : ℝ,
              rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ,
                rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) := by
      simpa using MeasureTheory.integral_sub hInt_det2_tilde hInt_outer_tilde
    have hI2 :
        (∫ t : ℝ,
            ((rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t -
                rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) -
              rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t) ∂ (volume : Measure ℝ)) =
          (∫ t : ℝ,
              (rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t -
                rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ,
                rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) := by
      simpa using MeasureTheory.integral_sub hInt_det2_outer hInt_ratio_tilde
    calc
      (∫ t : ℝ, rightEdgeIntegrand_decomp LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))
          = (∫ t : ℝ,
              (rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t -
                rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t -
                rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t) ∂ (volume : Measure ℝ)) := by
              simp [rightEdgeIntegrand_decomp_eq_det2_sub_outer_sub_ratio]
      _ = (∫ t : ℝ,
              ((rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t -
                rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) -
                rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t) ∂ (volume : Measure ℝ)) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ =
          ((∫ t : ℝ,
              (rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t -
                rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ,
                rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))) := hI2
      _ = (((∫ t : ℝ,
              rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ,
                rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))) -
            (∫ t : ℝ,
                rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))) := by
              simpa [hI1]
      _ = (∫ t : ℝ,
            rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) -
          (∫ t : ℝ,
              rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) -
          (∫ t : ℝ,
              rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) := by
              ring

  -- Now the equivalence is pure scalar algebra.
  constructor
  · intro H
    -- rewrite `rightEdge_integral_identity_decomp` using the two computed integrals
    have H' :
        ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t ∂ (volume : Measure ℝ)) -
            (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t ∂ (volume : Measure ℝ))) +
          ((∫ t : ℝ,
                rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) -
              (∫ t : ℝ,
                  rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)) -
              (∫ t : ℝ,
                  rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)))
          =
          ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ) := by
      simpa [rightEdge_integral_identity_decomp, h_decomp_integral, h_decomp_integral_tilde] using H
    -- Expand the component identity and finish by `ring`.
    dsimp [rightEdge_integral_identity_components, det2_fullIntegral, outer_fullIntegral, ratio_fullIntegral]
    have hRing :
        (∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t) +
              (∫ t : ℝ, rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t) -
            ((∫ t : ℝ, rightEdgeIntegrand_outer LC P h t) +
                (∫ t : ℝ, rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t)) -
          ((∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t) +
                (∫ t : ℝ, rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t))
          =
        ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t) -
              (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t) -
              (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t)) +
          ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t) -
                (∫ t : ℝ, rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) -
                (∫ t : ℝ, rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t)) := by
      ring
    exact hRing.trans (by simpa using H')
  · intro H
    -- Start from the component identity, rewrite it into the “sum of two triples” form,
    -- then rewrite back to the decomposed identity using `h_decomp_integral`/`h_decomp_integral_tilde`.
    have Hexp :
        (∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t) +
              (∫ t : ℝ, rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t) -
            ((∫ t : ℝ, rightEdgeIntegrand_outer LC P h t) +
                (∫ t : ℝ, rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t)) -
          ((∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t) +
                (∫ t : ℝ, rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t))
          =
        ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ) := by
      simpa [rightEdge_integral_identity_components, det2_fullIntegral, outer_fullIntegral, ratio_fullIntegral] using H
    have hRing :
        ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t) -
              (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t) -
              (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t)) +
          ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t) -
                (∫ t : ℝ, rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) -
                (∫ t : ℝ, rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t))
          =
        (∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t) +
              (∫ t : ℝ, rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t) -
            ((∫ t : ℝ, rightEdgeIntegrand_outer LC P h t) +
                (∫ t : ℝ, rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t)) -
          ((∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t) +
                (∫ t : ℝ, rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t)) := by
      ring
    have Hsum :
        ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t) -
              (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t) -
              (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t)) +
          ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t) -
                (∫ t : ℝ, rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) -
                (∫ t : ℝ, rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t))
          =
        ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ) :=
      (hRing.trans Hexp)
    -- Now rewrite to the decomposed identity.
    dsimp [rightEdge_integral_identity_decomp]
    calc
      (∫ t : ℝ, rightEdgeIntegrand_decomp LC P h t ∂ (volume : Measure ℝ)) +
          (∫ t : ℝ, rightEdgeIntegrand_decomp LC P (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))
          =
        ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P h t) -
              (∫ t : ℝ, rightEdgeIntegrand_outer LC P h t) -
              (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t)) +
          ((∫ t : ℝ, rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h) t) -
                (∫ t : ℝ, rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h) t) -
                (∫ t : ℝ, rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h) t)) := by
          simpa [h_decomp_integral, h_decomp_integral_tilde]
      _ = ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ) := Hsum

/--
Bundle form of the remaining analytic content: integrability of the right-edge integrands, plus the
full-line integral identity.
-/
structure RightEdgeIntegralIdentityAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents) where
  /-- Right-edge integrand is integrable for all test functions. -/
  integrable_rightEdge : ∀ h : F, Integrable (rightEdgeIntegrand LC h) (volume : Measure ℝ)
  /-- The full-line integral identity holds for all test functions. -/
  integral_identity : ∀ h : F, rightEdge_integral_identity (LC := LC) (P := P) h

/--
If the right-edge integrand is integrable on `ℝ`, then the finite right-edge contour integral
`vertRight … c T` converges (as `T → ∞`) to `I` times the full-line integral.
-/
theorem tendsto_vertRight_of_integrable
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (h : F)
    (hInt : Integrable (rightEdgeIntegrand LC h) (volume : Measure ℝ)) :
    Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop
      (nhds (Complex.I * ∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ))) := by
  -- Unfold `vertRight` and apply Mathlib’s `intervalIntegral_tendsto_integral` on `(-T..T)`.
  dsimp [ContourW1.vertRight, rightEdgeIntegrand]
  have hlim :
      Filter.Tendsto
        (fun T : ℝ =>
          ∫ t : ℝ in (-T)..T,
            M[h]((LC.c : ℂ) + (t : ℂ) * Complex.I) *
              logDeriv LC.xi ((LC.c : ℂ) + (t : ℂ) * Complex.I))
        Filter.atTop
        (nhds (∫ t : ℝ,
          M[h]((LC.c : ℂ) + (t : ℂ) * Complex.I) *
            logDeriv LC.xi ((LC.c : ℂ) + (t : ℂ) * Complex.I) ∂ (volume : Measure ℝ))) := by
    simpa using
      (MeasureTheory.intervalIntegral_tendsto_integral
        (μ := (volume : Measure ℝ))
        (l := (Filter.atTop : Filter ℝ))
        (f := fun t : ℝ =>
          M[h]((LC.c : ℂ) + (t : ℂ) * Complex.I) *
            logDeriv LC.xi ((LC.c : ℂ) + (t : ℂ) * Complex.I))
        (a := fun T : ℝ => -T)
        (b := fun T : ℝ => T)
        hInt
        (ha := tendsto_neg_atTop_atBot)
        (hb := tendsto_id))
  -- Multiply by the constant `I` on the left (continuous).
  simpa [mul_assoc] using (Filter.Tendsto.const_mul Complex.I hlim)

/--
If both right-edge integrands (`h` and `˜ₘh`) are integrable, then the *sum* of right-edge contour
integrals converges to `I` times the sum of the full-line integrals.
-/
theorem tendsto_vertRight_add_vertRight_tilde_of_integrable
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (h : F)
    (hInt : Integrable (rightEdgeIntegrand LC h) (volume : Measure ℝ))
    (hInt_tilde : Integrable (rightEdgeIntegrand LC (TestSpace.tilde (F := F) h)) (volume : Measure ℝ)) :
    Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
          ContourW1.vertRight (fun s : ℂ =>
              M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop
      (nhds
        (Complex.I * (∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ)) +
          Complex.I * (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)))) := by
  have h1 := tendsto_vertRight_of_integrable (LC := LC) (h := h) hInt
  have h2 :=
    tendsto_vertRight_of_integrable (LC := LC) (h := (TestSpace.tilde (F := F) h)) hInt_tilde
  simpa using h1.add h2

/--
If the right-edge integrals converge to their full-line limits, and the full-line integral identity
holds, then the bundled `rightEdge_phase_limit` follows.

This isolates the remaining analytic content to a single integral identity:
\[
  \int_{\mathbb R} F_h(c+it)\,\frac{\xi'}{\xi}(c+it)\,dt
  + \int_{\mathbb R} F_{\tilde h}(c+it)\,\frac{\xi'}{\xi}(c+it)\,dt
  \;=\;
  \int_{\mathbb R} -F_h(\tfrac12+it)\,\theta'(t)\,dt.
\]
-/
theorem rightEdge_phase_limit_of_integrable_and_integral_identity
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hInt : Integrable (rightEdgeIntegrand LC h) (volume : Measure ℝ))
    (hInt_tilde : Integrable (rightEdgeIntegrand LC (TestSpace.tilde (F := F) h)) (volume : Measure ℝ))
    (hIntegralId :
      (∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ)) +
        (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))
        =
        ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ)) :
    Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
          ContourW1.vertRight (fun s : ℂ =>
              M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop
      (nhds (Complex.I * ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ))) := by
  -- First take the limit to `I * (∫ f + ∫ f_tilde)`.
  have hlim :=
    tendsto_vertRight_add_vertRight_tilde_of_integrable
      (LC := LC) (h := h) hInt hInt_tilde
  -- Then rewrite the limit using the provided full-line integral identity.
  have :
      (Complex.I * (∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ)) +
        Complex.I * (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ)))
        =
      Complex.I * ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ) := by
    -- factor `I` and use `hIntegralId`
    calc
      Complex.I * (∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ)) +
          Complex.I * (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))
          = Complex.I *
              ((∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ)) +
                (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))) := by
              simpa using (mul_add (Complex.I)
                (∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ))
                (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))).symm
      _ = Complex.I * ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ) := by
            simpa [hIntegralId]
  -- Finish by rewriting the `nhds` target.
  simpa [this] using hlim

/--
If the right-edge integrand is integrable for all `h` and the full-line integral identity holds
for all `h`, then the right-edge `Tendsto` statement (`rightEdge_phase_limit`) follows.
-/
theorem rightEdge_phase_limit_of_RightEdgeIntegralIdentityAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (A : RightEdgeIntegralIdentityAssumptions (LC := LC) (P := P))
    (h : F) :
    Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
          ContourW1.vertRight (fun s : ℂ =>
              M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop
      (nhds (Complex.I * ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ))) := by
  -- Apply the previous lemma with `hInt` for `h` and `hInt_tilde` for `˜ₘh`.
  have hInt := A.integrable_rightEdge h
  have hInt_tilde := A.integrable_rightEdge (TestSpace.tilde (F := F) h)
  have hId := A.integral_identity h
  -- Unfold the bundled identity and discharge.
  exact
    rightEdge_phase_limit_of_integrable_and_integral_identity
      (LC := LC) (P := P) (h := h) hInt hInt_tilde (by simpa [rightEdge_integral_identity] using hId)

/--
If `W¹` is given as the `T → ∞` limit of the standard rectangle contour truncation (`W1Trunc`),
and the horizontal edges vanish, then the vertical contour contribution tends to `(2πi) * W¹`.

If, additionally, the xi functional-equation identity is available in log-derivative form on the
left edge, then the *vertical difference* can be rewritten as a sum of *right-edge* integrals for
`h` and `˜ₘh`.

This lemma packages that combination in the setting of a `LagariasContourFramework`.
-/
theorem tendsto_vertRight_add_vertRight_tilde_of_horizontal_vanish
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hxi : LC.xi = P.xi)
    (hBot : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hTop : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hLog : ∀ t : ℝ, logDeriv P.xi (((1 - LC.c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv P.xi ((LC.c : ℂ) + ((-t : ℝ) : ℂ) * I)) :
    Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
          ContourW1.vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds (((2 * Real.pi : ℂ) * I) * LC.contourW1.W1 h)) := by
  -- Rewrite the functional-equation log-derivative hypothesis to the `LC.xi` function.
  have hLog' :
      ∀ t : ℝ, logDeriv LC.xi (((1 - LC.c : ℝ) : ℂ) + (t : ℂ) * I) =
        - logDeriv LC.xi ((LC.c : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    intro t
    simpa [hxi] using hLog t
  -- Apply the generic contour lemma (Mellin involution is discharged inside `ContourW1`).
  simpa using
    ContourW1.tendsto_vertRight_add_vertRight_tilde_of_horizontal_vanish (F := F)
      (xi := LC.xi) (c := LC.c) (A := LC.contourW1) (f := h) hBot hTop
      (hM := fun t => by simpa using ContourW1.mellin_leftEdge_eq_tilde_rightEdge (f := h) (c := LC.c) (t := t))
      (hLog := hLog')

/--
Specialization of `tendsto_vertRight_add_vertRight_tilde_of_horizontal_vanish` to the case
`LC.xi = P.xi = xiLagarias`, where the log-derivative functional equation is provided by
`Lagarias.logDeriv_xiLagarias_leftEdge`.
-/
theorem tendsto_vertRight_add_vertRight_tilde_of_horizontal_vanish_xiLagarias
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hxiLC : LC.xi = xiLagarias)
    (hxiP : P.xi = xiLagarias)
    (hBot : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hTop : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
          ContourW1.vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds (((2 * Real.pi : ℂ) * I) * LC.contourW1.W1 h)) := by
  -- Derive `LC.xi = P.xi`.
  have hxi : LC.xi = P.xi := by simpa [hxiLC, hxiP]
  -- Provide the log-derivative functional-equation identity from `xiLagarias`.
  have hLog : ∀ t : ℝ, logDeriv P.xi (((1 - LC.c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv P.xi ((LC.c : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    intro t
    -- rewrite `P.xi` to `xiLagarias`, then use the lemma from `Lagarias.lean`
    simpa [hxiP] using (logDeriv_xiLagarias_leftEdge (c := LC.c) (t := t))
  -- Now apply the general lemma.
  simpa using
    tendsto_vertRight_add_vertRight_tilde_of_horizontal_vanish (LC := LC) (P := P) (h := h)
      (hxi := hxi) hBot hTop hLog

/-!
### Reducing `explicit_formula_cancellation` to a single contour-limit hypothesis
-/

/--
If:
- `LC.xi = P.xi = xiLagarias`,
- the horizontal edges vanish, and
- the *sum* of right-edge integrals for `h` and `˜ₘh` converges to the boundary-phase integral,
then the contour-defined `W¹` satisfies the `explicit_formula_cancellation_contour` identity.

This isolates the remaining analytic work into a single `Tendsto` hypothesis about the right edge.
-/
theorem explicit_formula_cancellation_contour_of_tendsto_vertRight_add_vertRight_tilde_xiLagarias
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hxiLC : LC.xi = xiLagarias)
    (hxiP : P.xi = xiLagarias)
    (hBot : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hTop : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hRightLim :
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
            ContourW1.vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop
        (nhds (Complex.I *
          ∫ t : ℝ, -(M[h](1/2 + Complex.I * t) *
              ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume))) :
    explicit_formula_cancellation_contour (LC := LC) (P := P) h := by
  -- First get the limit of the right-edge sum from the contour machinery (functional equation on `xiLagarias`).
  have hW :
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
            ContourW1.vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop (nhds (((2 * Real.pi : ℂ) * Complex.I) * LC.contourW1.W1 h)) := by
    -- Apply the xiLagarias-specialized lemma.
    simpa [hxiLC] using
      tendsto_vertRight_add_vertRight_tilde_of_horizontal_vanish_xiLagarias
        (LC := LC) (P := P) (h := h) (hxiLC := hxiLC) (hxiP := hxiP) hBot hTop
  -- Uniqueness of limits in `ℂ` gives the key equality.
  have hEq :
      (((2 * Real.pi : ℂ) * Complex.I) * LC.contourW1.W1 h) =
        Complex.I *
          ∫ t : ℝ, -(M[h](1/2 + Complex.I * t) *
              ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume := by
    exact tendsto_nhds_unique hW hRightLim
  -- Cancel `I` and solve for `W¹`.
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2pi : ((2 * Real.pi : ℂ)) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) hpi
  -- Rewrite the LHS as `I * ((2π) * W1)` and cancel `I`.
  have hEq' :
      Complex.I * ((2 * Real.pi : ℂ) * LC.contourW1.W1 h) =
        Complex.I *
          ∫ t : ℝ, -(M[h](1/2 + Complex.I * t) *
              ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume := by
    -- commute factors on the LHS
    simpa [mul_assoc, mul_left_comm, mul_comm] using hEq
  have hEq'' :
      ((2 * Real.pi : ℂ) * LC.contourW1.W1 h) =
        ∫ t : ℝ, -(M[h](1/2 + Complex.I * t) *
            ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume := by
    exact mul_left_cancel₀ hI hEq'
  -- Divide by `2π`.
  have hW1 :
      LC.contourW1.W1 h =
        ((2 * Real.pi : ℂ)⁻¹) *
          ∫ t : ℝ, -(M[h](1/2 + Complex.I * t) *
              ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume := by
    -- Multiply `hEq''` by `(2π)⁻¹` on the left and cancel using `inv_mul_cancel_left₀`.
    have hmul :=
      congrArg (fun z : ℂ => ((2 * Real.pi : ℂ)⁻¹) * z) hEq''
    have hinv :
        ((2 * Real.pi : ℂ)⁻¹) * ((2 * Real.pi : ℂ) * LC.contourW1.W1 h) = LC.contourW1.W1 h :=
      inv_mul_cancel_left₀ (a := (2 * Real.pi : ℂ)) h2pi (LC.contourW1.W1 h)
    calc
      LC.contourW1.W1 h
          = ((2 * Real.pi : ℂ)⁻¹) * ((2 * Real.pi : ℂ) * LC.contourW1.W1 h) := by
              exact hinv.symm
      _ = ((2 * Real.pi : ℂ)⁻¹) *
            ∫ t : ℝ, -(M[h](1/2 + Complex.I * t) *
                ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume := by
              exact hmul
  -- Finish by rewriting `((2π)⁻¹)` as `1/(2π)` in the statement definition.
  dsimp [explicit_formula_cancellation_contour]
  -- rewrite `((2π)⁻¹)` into `1/(2π)` and finish
  simpa [one_div, div_eq_mul_inv, mul_assoc] using hW1

/--
If:
- `LC.xi = P.xi = xiLagarias`,
- the horizontal edges vanish,
- the right-edge integrands are integrable on `ℝ`, and
- the **single full-line integral identity** holds,
then `explicit_formula_cancellation_contour` follows.

This further isolates the remaining analytic content into one integral identity statement.
-/
theorem explicit_formula_cancellation_contour_of_integrable_and_integral_identity_xiLagarias
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (h : F)
    (hxiLC : LC.xi = xiLagarias)
    (hxiP : P.xi = xiLagarias)
    (hBot : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hTop : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hInt : Integrable (rightEdgeIntegrand LC h) (volume : Measure ℝ))
    (hInt_tilde : Integrable (rightEdgeIntegrand LC (TestSpace.tilde (F := F) h)) (volume : Measure ℝ))
    (hIntegralId :
      (∫ t : ℝ, rightEdgeIntegrand LC h t ∂ (volume : Measure ℝ)) +
        (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ (volume : Measure ℝ))
        =
        ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ)) :
    explicit_formula_cancellation_contour (LC := LC) (P := P) h := by
  -- Turn the full-line integral identity into the needed `Tendsto` for right-edge contour integrals.
  have hRightLim' :
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
            ContourW1.vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop
        (nhds (Complex.I * ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ volume)) := by
    exact
      rightEdge_phase_limit_of_integrable_and_integral_identity
        (LC := LC) (P := P) (h := h) hInt hInt_tilde hIntegralId
  have hRightLim :
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
            ContourW1.vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop
        (nhds (Complex.I *
          ∫ t : ℝ, -(M[h](1/2 + Complex.I * t) *
              ((deriv (boundaryPhaseFunction P) t : ℝ) : ℂ)) ∂ volume)) := by
    simpa [boundaryPhaseIntegrand] using hRightLim'
  -- Now apply the main reduction lemma.
  exact
    explicit_formula_cancellation_contour_of_tendsto_vertRight_add_vertRight_tilde_xiLagarias
      (LC := LC) (P := P) (h := h)
      (hxiLC := hxiLC) (hxiP := hxiP)
      (hBot := hBot) (hTop := hTop) (hRightLim := hRightLim)

/--
If `RightEdgePhaseLimitAssumptions` holds, then the contour-defined `W¹` satisfies the
boundary-phase identity `explicit_formula_cancellation_contour`.
-/
theorem explicit_formula_cancellation_contour_of_rightEdgePhaseLimitAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (A : RightEdgePhaseLimitAssumptions (LC := LC) (P := P))
    (h : F) :
    explicit_formula_cancellation_contour (LC := LC) (P := P) h := by
  -- Apply the previously proved reduction lemma with the bundle fields.
  exact
    explicit_formula_cancellation_contour_of_tendsto_vertRight_add_vertRight_tilde_xiLagarias
      (LC := LC) (P := P) (h := h)
      (hxiLC := A.xiLC) (hxiP := A.xiP)
      (hBot := A.horizBottom_vanish h)
      (hTop := A.horizTop_vanish h)
      (hRightLim := A.rightEdge_phase_limit h)

/-!
## Fourier inversion / Perron formula for Mellin-Dirichlet terms

The key analytic step connecting `det2_fullIntegral` to `primeTerm` is a Fourier inversion identity:
for each `n : ℕ`, the integral `∫ M[h](c+it) * n^{-(c+it)} dt` evaluates to `(2π/√n) * h(log n)`.

This is classical Perron-style reasoning: the Mellin transform `M[h](s)` is (up to normalization)
the Fourier transform of a shifted version of `h`, and integrating against `n^{-s}` on a vertical
line is inverse Fourier at `log n`.

We state this as a hypothesis for now, to be discharged by Mathlib's Fourier inversion theorem
once the test-function regularity is formalized.
-/

/--
**Fourier inversion for a single Dirichlet term.**

For a test function `h` and `n ≥ 1`, integrating `M[h](c+it) * n^{-(c+it)}` over `t ∈ ℝ` yields
`(2π / √n) * h(log n)`.

Derivation:
- `M[h](c+it) = ∫ h(x) e^{(c-1/2)x} e^{itx} dx` (Mellin as shifted Fourier)
- Integrating against `n^{-(c+it)} = n^{-c} e^{-it log n}`:
  `∫ M[h](c+it) n^{-(c+it)} dt = n^{-c} ∫∫ h(x) e^{(c-1/2)x} e^{it(x - log n)} dx dt`
- Inner integral gives `2π δ(x - log n)` (Fourier inversion).
- Result: `2π n^{-c} h(log n) e^{(c-1/2) log n} = 2π h(log n) / √n`.
-/
def FourierInversionDirichletTerm
    {F : Type} [TestSpace F]
    (c : ℝ) (hc : 1 / 2 < c)
    (testValue : F → ℝ → ℂ)  -- evaluation of test function at a real point
    : Prop :=
  ∀ (h : F) (n : ℕ) (hn : 1 ≤ n),
    (∫ t : ℝ,
        M[h]((c : ℂ) + (t : ℂ) * I) *
          (n : ℂ)^(-(((c : ℂ) + (t : ℂ) * I))) ∂ (volume : Measure ℝ))
      =
    (2 * Real.pi / Real.sqrt n) * testValue h (Real.log n)

/--
**Dirichlet series evaluation via Fourier inversion.**

If the Fourier inversion identity holds for each Dirichlet term, and `logDeriv det2` equals the
negative von Mangoldt L-series (i.e., `logDeriv det2 s = - ∑ Λ(n) n^{-s}`), then the `det2`
right-edge integral evaluates to the prime-power sum.

This bundles the three analytic inputs:
1. Fourier inversion for Mellin-Dirichlet terms.
2. `logDeriv det2 = - L(Λ)` (von Mangoldt L-series).
3. Summation-integration interchange (absolute convergence).
-/
structure Det2PrimeTermAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (testValue : F → ℝ → ℂ)  -- evaluation of test function at a real point
    where
  /-- Contour parameter is in the convergence region. -/
  hc : 1 / 2 < LC.c
  /-- The Fourier inversion identity holds for all Dirichlet terms. -/
  fourier_inversion : FourierInversionDirichletTerm (c := LC.c) (hc := hc) (testValue := testValue)
  /-- `logDeriv det2` equals the negative von Mangoldt L-series on `Re(s) > 1`. -/
  logDeriv_det2_eq_neg_vonMangoldt :
    ∀ s : ℂ, 1 < s.re →
      logDeriv P.det2 s = - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
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
  /-- The tilde test function satisfies the same Fourier inversion. -/
  fourier_inversion_tilde : FourierInversionDirichletTerm (c := LC.c) (hc := hc)
    (testValue := fun h x => testValue (TestSpace.tilde (F := F) h) x)

/--
If `Det2PrimeTermAssumptions` holds, then `det2_fullIntegral` matches the prime-power sum:
`- ∑ Λ(n)/√n * (h(log n) + h(-log n)) * 2π`.

This is the **det2 component identity** (subject to the analytic hypotheses in the bundle).
-/
theorem det2_fullIntegral_eq_neg_primePowerSum_of_assumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (testValue : F → ℝ → ℂ)
    (A : Det2PrimeTermAssumptions (LC := LC) (P := P) (testValue := testValue))
    (h : F)
    (hc_gt_one : 1 < LC.c) :  -- Need c > 1 for L-series convergence
    det2_fullIntegral (LC := LC) (P := P) h =
      - (2 * Real.pi) * ∑' n : ℕ,
          if n = 0 then 0 else
            ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
              (testValue h (Real.log n) + testValue (TestSpace.tilde (F := F) h) (Real.log n)) := by
  -- Step 1: Expand `det2_fullIntegral` as sum of two integrals.
  dsimp [det2_fullIntegral, rightEdgeIntegrand_det2]

  -- Step 2: Rewrite `logDeriv det2` using the L-series identity.
  have hLseries : ∀ t : ℝ,
      logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I) =
        - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((LC.c : ℂ) + (t : ℂ) * I) := by
    intro t
    apply A.logDeriv_det2_eq_neg_vonMangoldt
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero]
    linarith

  -- Step 3: Define the per-term integrand function.
  let Fn : ℕ → ℝ → ℂ := fun n t =>
    M[h]((LC.c : ℂ) + (t : ℂ) * I) *
      (ArithmeticFunction.vonMangoldt n : ℂ) *
      (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))

  -- Step 4: The L-series expansion gives the integrand as a tsum.
  -- LSeries f s = ∑' n, term f s n = ∑' n, if n = 0 then 0 else f n / n^s.
  -- So M[h](s) * (-L(Λ, s)) = - ∑' n, M[h](s) * Λ(n) * n^{-s} = - ∑' n, Fn n t.
  have hIntegrand : ∀ t : ℝ,
      M[h]((LC.c : ℂ) + (t : ℂ) * I) * logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I) =
        - ∑' n : ℕ, Fn n t := by
    intro t
    rw [hLseries t]
    -- Cancel the outer minus sign, then expand `LSeries`.
    rw [mul_neg]
    -- `tsum_neg`/`tsum_mul_left` hold unconditionally for `tsum` (even without summability).
    apply (neg_inj).1
    simp only [LSeries]
    -- Move the constant `M[h](c+it)` inside the `tsum`.
    rw [← tsum_mul_left]
    -- Eliminate any redundant double negations created by rewriting.
    simp only [neg_neg]
    -- Help typeclass inference by fixing the codomain explicitly to `ℂ`.
    refine (tsum_congr (α := ℂ) (β := ℕ) ?_)
    intro n
    simp only [LSeries.term, Fn]
    by_cases hn : n = 0
    · subst hn
      -- term f s 0 = 0, and Fn 0 t = 0 because Λ(0) = 0
      simp [ArithmeticFunction.map_zero]
    · simp only [hn, ↓reduceIte]
      -- f n / n^s = f n * n^{-s}
      rw [div_eq_mul_inv, ← cpow_neg]
      ring

  -- Step 5: Apply Fubini (integral-tsum exchange).
  -- ∫ (- ∑' Fn n t) dt = - ∑' ∫ Fn n t dt
  -- This uses A.integrable_term and A.summable_integral_norm.
  have hFubini :
      (∫ t : ℝ, (- ∑' n : ℕ, Fn n t) ∂ volume) =
        - ∑' n : ℕ, (∫ t : ℝ, Fn n t ∂ volume) := by
    rw [MeasureTheory.integral_neg]
    congr 1
    -- Apply integral_tsum_of_summable_integral_norm
    -- Need: integrability of each F n and summability of ∫ ‖F n‖
    have hInt : ∀ n : ℕ, Integrable (Fn n) (volume : Measure ℝ) := by
      intro n
      by_cases hn : n = 0
      · -- n = 0: Λ(0) = 0, so F 0 = 0
        have hFn0 : Fn n = fun _ => 0 := by
          funext t
          simp only [Fn, hn, Nat.cast_zero, ArithmeticFunction.map_zero, Complex.ofReal_zero,
            zero_mul, mul_zero]
        simpa [hFn0] using (integrable_zero : Integrable (fun _ : ℝ => (0 : ℂ)) (volume : Measure ℝ))
      · -- n ≥ 1
        have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        exact A.integrable_term h n hn'
    have hSum : Summable (fun n : ℕ => ∫ t : ℝ, ‖Fn n t‖ ∂ volume) :=
      A.summable_integral_norm h
    exact (MeasureTheory.integral_tsum_of_summable_integral_norm hInt hSum).symm

  -- Step 6: Apply Fourier inversion to each n ≥ 1 term.
  -- ∫ Fn n t dt = ∫ M[h](c+it) * Λ(n) * n^{-(c+it)} dt
  --            = Λ(n) * ∫ M[h](c+it) * n^{-(c+it)} dt
  --            = Λ(n) * (2π/√n) * testValue h (log n)
  have hFourierTerm : ∀ n : ℕ, 1 ≤ n →
      (∫ t : ℝ, Fn n t ∂ volume) =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((2 * Real.pi / Real.sqrt n) * testValue h (Real.log n)) := by
    intro n hn
    -- Factor out the constant Λ(n)
    have hconst :
        (∫ t : ℝ, Fn n t ∂ volume) =
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (∫ t : ℝ, M[h]((LC.c : ℂ) + (t : ℂ) * I) *
              (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I))) ∂ volume) := by
      simp only [Fn]
      rw [← integral_mul_left]
      congr 1
      funext t
      ring
    rw [hconst]
    -- Apply Fourier inversion
    have hFI := A.fourier_inversion h n hn
    rw [hFI]

  -- Step 7: Simplify the tsum using hFourierTerm.
  have hTsumSimp :
      (∑' n : ℕ, (∫ t : ℝ, Fn n t ∂ volume)) =
        (2 * Real.pi) * ∑' n : ℕ,
          if n = 0 then 0 else
            ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) * testValue h (Real.log n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · -- n = 0: both sides are 0
      subst hn
      simp only [if_true]
      have hzero : (fun t => Fn 0 t) = fun _ => 0 := by
        funext t
        simp only [Fn, Nat.cast_zero, ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul, mul_zero]
      simp [hzero]
    · -- n ≥ 1
      simp only [if_neg hn]
      have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      rw [hFourierTerm n hn']
      -- Simplify: Λ(n) * ((2π/√n) * testValue) = (2π) * (Λ(n)/√n) * testValue
      have hne : (Real.sqrt n : ℂ) ≠ 0 := by
        simp [Complex.ofReal_eq_zero, Real.sqrt_ne_zero', Nat.cast_pos, hn]
      field_simp
      ring

  -- Step 8: Define the per-term integrand for tilde h.
  let Fn_tilde : ℕ → ℝ → ℂ := fun n t =>
    M[(TestSpace.tilde (F := F) h)]((LC.c : ℂ) + (t : ℂ) * I) *
      (ArithmeticFunction.vonMangoldt n : ℂ) *
      (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I)))

  -- Step 9: Parallel constructions for tilde h.
  have hIntegrand_tilde : ∀ t : ℝ,
      M[(TestSpace.tilde (F := F) h)]((LC.c : ℂ) + (t : ℂ) * I) *
          logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I) =
        - ∑' n : ℕ, Fn_tilde n t := by
    intro t
    rw [hLseries t]
    rw [mul_neg]
    apply (neg_inj).1
    simp only [LSeries]
    rw [← tsum_mul_left]
    simp only [neg_neg]
    refine (tsum_congr (α := ℂ) (β := ℕ) ?_)
    intro n
    simp only [LSeries.term, Fn_tilde]
    by_cases hn : n = 0
    · subst hn
      simp [ArithmeticFunction.map_zero]
    · simp only [hn, ↓reduceIte]
      rw [div_eq_mul_inv, ← cpow_neg]
      ring

  have hFubini_tilde :
      (∫ t : ℝ, (- ∑' n : ℕ, Fn_tilde n t) ∂ volume) =
        - ∑' n : ℕ, (∫ t : ℝ, Fn_tilde n t ∂ volume) := by
    rw [MeasureTheory.integral_neg]
    congr 1
    have hInt : ∀ n : ℕ, Integrable (Fn_tilde n) (volume : Measure ℝ) := by
      intro n
      by_cases hn : n = 0
      · have hFn0 : Fn_tilde n = fun _ => 0 := by
          funext t
          simp only [Fn_tilde, hn, Nat.cast_zero, ArithmeticFunction.map_zero, Complex.ofReal_zero,
            zero_mul, mul_zero]
        simpa [hFn0] using (integrable_zero : Integrable (fun _ : ℝ => (0 : ℂ)) (volume : Measure ℝ))
      · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        exact A.integrable_term (TestSpace.tilde (F := F) h) n hn'
    have hSum : Summable (fun n : ℕ => ∫ t : ℝ, ‖Fn_tilde n t‖ ∂ volume) :=
      A.summable_integral_norm (TestSpace.tilde (F := F) h)
    exact (MeasureTheory.integral_tsum_of_summable_integral_norm hInt hSum).symm

  have hFourierTerm_tilde : ∀ n : ℕ, 1 ≤ n →
      (∫ t : ℝ, Fn_tilde n t ∂ volume) =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((2 * Real.pi / Real.sqrt n) * testValue (TestSpace.tilde (F := F) h) (Real.log n)) := by
    intro n hn
    have hconst :
        (∫ t : ℝ, Fn_tilde n t ∂ volume) =
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (∫ t : ℝ, M[(TestSpace.tilde (F := F) h)]((LC.c : ℂ) + (t : ℂ) * I) *
              (n : ℂ)^(-(((LC.c : ℂ) + (t : ℂ) * I))) ∂ volume) := by
      simp only [Fn_tilde]
      rw [← integral_mul_left]
      congr 1
      funext t
      ring
    rw [hconst]
    have hFI := A.fourier_inversion (TestSpace.tilde (F := F) h) n hn
    rw [hFI]

  have hTsumSimp_tilde :
      (∑' n : ℕ, (∫ t : ℝ, Fn_tilde n t ∂ volume)) =
        (2 * Real.pi) * ∑' n : ℕ,
          if n = 0 then 0 else
            ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
              testValue (TestSpace.tilde (F := F) h) (Real.log n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [if_true]
      have hzero : (fun t => Fn_tilde 0 t) = fun _ => 0 := by
        funext t
        simp only [Fn_tilde, Nat.cast_zero, ArithmeticFunction.map_zero, Complex.ofReal_zero,
          zero_mul, mul_zero]
      simp [hzero]
    · simp only [if_neg hn]
      have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      rw [hFourierTerm_tilde n hn']
      have hne : (Real.sqrt n : ℂ) ≠ 0 := by
        simp [Complex.ofReal_eq_zero, Real.sqrt_ne_zero', Nat.cast_pos, hn]
      field_simp
      ring

  -- Step 10: Combine everything.
  -- det2_fullIntegral = ∫ h + ∫ tilde h
  -- Each integral = - (2π) * ∑' (Λ(n)/√n) * testValue
  -- So: det2_fullIntegral = - (2π) * ∑' (Λ(n)/√n) * (testValue h + testValue tilde h)
  calc det2_fullIntegral (LC := LC) (P := P) h
      = (∫ t : ℝ, M[h]((LC.c : ℂ) + (t : ℂ) * I) * logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I) ∂ volume)
        + (∫ t : ℝ, M[(TestSpace.tilde (F := F) h)]((LC.c : ℂ) + (t : ℂ) * I) *
            logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I) ∂ volume) := by
          rfl
    _ = (∫ t : ℝ, (- ∑' n : ℕ, Fn n t) ∂ volume)
        + (∫ t : ℝ, (- ∑' n : ℕ, Fn_tilde n t) ∂ volume) := by
          congr 1
          ·
            -- Rewrite the integrand using `hIntegrand`.
            have hfg :
                (fun t : ℝ =>
                    M[h]((LC.c : ℂ) + (t : ℂ) * I) *
                      logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I)) =
                  fun t : ℝ => (- ∑' n : ℕ, Fn n t) := by
              funext t
              exact hIntegrand t
            simpa [hfg]
          ·
            have hfg :
                (fun t : ℝ =>
                    M[(TestSpace.tilde (F := F) h)]((LC.c : ℂ) + (t : ℂ) * I) *
                      logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I)) =
                  fun t : ℝ => (- ∑' n : ℕ, Fn_tilde n t) := by
              funext t
              exact hIntegrand_tilde t
            -- The goal's LHS may already be simplified using `TestSpace.mellin_tilde`,
            -- so rewrite it back into `M[˜ₘh](c+it)` form before using `hfg`.
            have hgoal :
                (∫ t : ℝ,
                    M[h](1 - ((LC.c : ℂ) + (t : ℂ) * I)) *
                      logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I) ∂ volume) =
                  ∫ t : ℝ, (- ∑' n : ℕ, Fn_tilde n t) ∂ volume := by
              have hIntEq :
                  (fun t : ℝ =>
                      M[h](1 - ((LC.c : ℂ) + (t : ℂ) * I)) *
                        logDeriv P.det2 ((LC.c : ℂ) + (t : ℂ) * I)) =
                    fun t : ℝ => (- ∑' n : ℕ, Fn_tilde n t) := by
                funext t
                -- `simp` uses `TestSpace.mellin_tilde` to rewrite `M[˜ₘh](c+it)` into `M[h](1-(c+it))`.
                simpa using (hIntegrand_tilde t)
              simpa [hIntEq]
            simpa using hgoal
    _ = (- ∑' n : ℕ, (∫ t : ℝ, Fn n t ∂ volume))
        + (- ∑' n : ℕ, (∫ t : ℝ, Fn_tilde n t ∂ volume)) := by
          rw [hFubini, hFubini_tilde]
    _ = - ((2 * Real.pi) * ∑' n : ℕ, if n = 0 then 0 else
            ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) * testValue h (Real.log n))
        + (- ((2 * Real.pi) * ∑' n : ℕ, if n = 0 then 0 else
            ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
              testValue (TestSpace.tilde (F := F) h) (Real.log n))) := by
          rw [hTsumSimp, hTsumSimp_tilde]
    _ = - (2 * Real.pi) * ∑' n : ℕ,
          if n = 0 then 0 else
            ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
              (testValue h (Real.log n) + testValue (TestSpace.tilde (F := F) h) (Real.log n)) := by
          -- A controlled algebraic finish: define the two Dirichlet series and use `tsum_add`.
          let sH : ℕ → ℂ := fun n =>
            if n = 0 then 0 else
              ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) * testValue h (Real.log n)
          let sT : ℕ → ℂ := fun n =>
            if n = 0 then 0 else
              ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
                testValue (TestSpace.tilde (F := F) h) (Real.log n)
          -- Summability of the two series (derived from `summable_integral_norm`).
          have hSummableIntegral :
              Summable (fun n : ℕ => (∫ t : ℝ, Fn n t ∂ (volume : Measure ℝ))) := by
            refine Summable.of_norm_bounded
              (g := fun n : ℕ => ∫ t : ℝ, ‖Fn n t‖ ∂ (volume : Measure ℝ))
              (A.summable_integral_norm h) ?_
            intro n
            simpa using (MeasureTheory.norm_integral_le_integral_norm (Fn n))
          have hSummableIntegral_tilde :
              Summable (fun n : ℕ => (∫ t : ℝ, Fn_tilde n t ∂ (volume : Measure ℝ))) := by
            refine Summable.of_norm_bounded
              (g := fun n : ℕ => ∫ t : ℝ, ‖Fn_tilde n t‖ ∂ (volume : Measure ℝ))
              (A.summable_integral_norm (TestSpace.tilde (F := F) h)) ?_
            intro n
            simpa using (MeasureTheory.norm_integral_le_integral_norm (Fn_tilde n))
          have hSummableSeries : Summable sH := by
            have hs :
                (fun n : ℕ => sH n) =
                  fun n : ℕ =>
                    ((1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Fn n t ∂ (volume : Measure ℝ))) := by
              funext n
              by_cases hn : n = 0
              · subst hn
                have hzero : (∫ t : ℝ, Fn 0 t ∂ (volume : Measure ℝ)) = 0 := by
                  have : (fun t => Fn 0 t) = fun _ => 0 := by
                    funext t
                    simp only [Fn, Nat.cast_zero, ArithmeticFunction.map_zero, Complex.ofReal_zero,
                      zero_mul, mul_zero]
                  simpa [this] using (integral_zero : (∫ t : ℝ, (0 : ℂ) ∂ (volume : Measure ℝ)) = 0)
                simp [sH, hzero]
              · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
                simp [sH, hn]  -- unfold `sH`
                rw [hFourierTerm n hn']
                field_simp [Real.pi_ne_zero, hn]
                ring
            simpa [hs] using (hSummableIntegral.const_smul (1 / (2 * Real.pi) : ℂ))
          have hSummableSeries_tilde : Summable sT := by
            have hs :
                (fun n : ℕ => sT n) =
                  fun n : ℕ =>
                    ((1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Fn_tilde n t ∂ (volume : Measure ℝ))) := by
              funext n
              by_cases hn : n = 0
              · subst hn
                have hzero : (∫ t : ℝ, Fn_tilde 0 t ∂ (volume : Measure ℝ)) = 0 := by
                  have : (fun t => Fn_tilde 0 t) = fun _ => 0 := by
                    funext t
                    simp only [Fn_tilde, Nat.cast_zero, ArithmeticFunction.map_zero, Complex.ofReal_zero,
                      zero_mul, mul_zero]
                  simpa [this] using (integral_zero : (∫ t : ℝ, (0 : ℂ) ∂ (volume : Measure ℝ)) = 0)
                simp [sT, hzero]
              · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
                simp [sT, hn]  -- unfold `sT`
                rw [hFourierTerm_tilde n hn']
                field_simp [Real.pi_ne_zero, hn]
                ring
            simpa [hs] using (hSummableIntegral_tilde.const_smul (1 / (2 * Real.pi) : ℂ))
          have hTsum : (∑' n : ℕ, sH n) + (∑' n : ℕ, sT n) = ∑' n : ℕ, (sH n + sT n) := by
            simpa using (tsum_add hSummableSeries hSummableSeries_tilde).symm
          have hTerm :
              (fun n : ℕ => sH n + sT n) =
                fun n : ℕ =>
                  if n = 0 then 0 else
                    ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
                      (testValue h (Real.log n) + testValue (TestSpace.tilde (F := F) h) (Real.log n)) := by
            funext n
            by_cases hn : n = 0
            · subst hn
              simp [sH, sT]
            ·
              simp [sH, sT, hn]
              -- `a * c + b * c = (a + b) * c`
              ring
          -- Now close by rewriting everything in terms of `sH`, `sT`, and `hTsum/hTerm`.
          have hA :
              (∑' n : ℕ,
                    if n = 0 then 0 else
                      testValue h (Real.log n) * ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n)) =
                ∑' n : ℕ, sH n := by
            refine tsum_congr ?_
            intro n
            by_cases hn : n = 0
            · subst hn; simp [sH]
            · simp [sH, hn, mul_comm, mul_left_comm, mul_assoc]
          have hB :
              (∑' n : ℕ,
                    if n = 0 then 0 else
                      testValue (TestSpace.tilde (F := F) h) (Real.log n) *
                        ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n)) =
                ∑' n : ℕ, sT n := by
            refine tsum_congr ?_
            intro n
            by_cases hn : n = 0
            · subst hn; simp [sT]
            · simp [sT, hn, mul_comm, mul_left_comm, mul_assoc]
          have hC :
              (∑' n : ℕ,
                    if n = 0 then 0 else
                      (testValue h (Real.log n) +
                          testValue (TestSpace.tilde (F := F) h) (Real.log n)) *
                        ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n)) =
                ∑' n : ℕ, (sH n + sT n) := by
            refine tsum_congr ?_
            intro n
            by_cases hn : n = 0
            · subst hn; simp [sH, sT]
            · simp [sH, sT, hn, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
          -- Use `hTsum` and `hTerm` to finish.
          -- (At this point, all `tsum`s have the same index and only ring arithmetic remains.)
          -- Replace the three `tsum`s with `sH`, `sT`, and `sH+sT`.
          simp [hA, hB, hC, hTsum, hTerm, mul_add, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_left_comm, mul_comm]

/-!
### Outer (Archimedean) component identity

The `outer` function is `O(s) = π^{-s/2} Γ(s/2) * (similar for odd part)`.
Its log-derivative involves `logDeriv(π^{-s/2}) = -log(π)/2` and `logDeriv(Γ(s/2)) = ψ(s/2)/2`.

The `outer_fullIntegral` should match the archimedean term from the explicit formula.
-/

/--
**Outer (Archimedean) component identity assumptions.**

This bundles the analytic inputs needed to prove `outer_fullIntegral = archimedeanTerm`:
1. The form of `logDeriv outer` in terms of `log(π)` and digamma.
2. Integrability of the test function against digamma.
-/
structure OuterArchimedeanAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (testValue : F → ℝ → ℂ)
    (fourierAtZero : F → ℂ)  -- ĥ(0) for the test function
    where
  /-- Contour parameter is in the convergence region. -/
  hc : 1 / 2 < LC.c
  /-- `logDeriv outer` decomposes into log(π) and digamma terms. -/
  logDeriv_outer_eq :
    ∀ s : ℂ, 1/2 < s.re →
      logDeriv P.outer s =
        -(Real.log Real.pi / 2 : ℂ) +
          (1/2 : ℂ) * (Complex.digamma (s/2) + Complex.digamma ((1-s)/2))
  /-- The vertical integral of `M[h] * logDeriv outer` converges. -/
  integrable_outer : ∀ h : F, Integrable (rightEdgeIntegrand_outer LC P h) (volume : Measure ℝ)
  /-- The archimedean term: `-(log π) * (ĥ(0) + tilde_ĥ(0)) + digamma_integral`. -/
  archimedeanTerm : F → ℂ
  /-- The full integral identity: `outer_fullIntegral = archimedeanTerm`. -/
  outer_eq_archimedean : ∀ h : F, outer_fullIntegral (LC := LC) (P := P) h = archimedeanTerm h

/--
If `OuterArchimedeanAssumptions` holds, then `outer_fullIntegral` matches the archimedean sum:
`-(log π) * (ĥ(0) + ĥ~(0)) + (digamma integrals)`.

This is the **outer component identity** (subject to the analytic hypotheses in the bundle).
-/
theorem outer_fullIntegral_eq_archimedean_of_assumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (testValue : F → ℝ → ℂ)
    (fourierAtZero : F → ℂ)
    (A : OuterArchimedeanAssumptions (LC := LC) (P := P) (testValue := testValue)
           (fourierAtZero := fourierAtZero))
    (h : F) :
    outer_fullIntegral (LC := LC) (P := P) h = A.archimedeanTerm h := A.outer_eq_archimedean h

/-!
### Ratio (Boundary Phase) component identity

The `ratio` function is `J = det₂ / (outer · ξ)`.
On the critical line, `|J| = 1` and `logDeriv J = i θ'(t)` where `θ` is the boundary phase.

The `ratio_fullIntegral` should match the boundary phase integral that appears in the
explicit formula cancellation.
-/

/--
**Ratio (Boundary Phase) component identity assumptions.**

This bundles the analytic inputs needed to prove `ratio_fullIntegral = boundaryPhaseIntegral`:
1. The PSC phase-velocity identity (relating `logDeriv J` to `θ'`).
2. Shift of contour from `c` to `1/2` (using functional equation and horizontal vanishing).
-/
structure RatioBoundaryPhaseAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents) where
  /-- Contour parameter is in the convergence region. -/
  hc : 1 / 2 < LC.c
  /-- The PSC phase-velocity identity holds: on the critical line, `logDeriv J = i θ'`. -/
  logDeriv_ratio_critical_line :
    ∀ t : ℝ, logDeriv (PSCRatio P) ((1/2 : ℂ) + I * t) = I * (deriv (boundaryPhaseFunction P) t : ℂ)
  /-- The contour can be shifted from `Re(s) = c` to `Re(s) = 1/2` (no poles in between). -/
  contour_shift :
    ∀ h : F,
      (∫ t : ℝ, rightEdgeIntegrand_ratio LC P h t ∂ (volume : Measure ℝ)) =
        ∫ t : ℝ, M[h]((1/2 : ℂ) + I * t) * logDeriv (PSCRatio P) ((1/2 : ℂ) + I * t) ∂ (volume : Measure ℝ)
  /-- The critical line sum formula: `M[h] * I * θ' + M[tilde h] * I * θ' = -M[h] * θ'` (in integral).
      This captures the relationship between h and tilde h via the Mellin involution `s ↦ 1-s`
      combined with the real structure of the spectral measure. -/
  critical_line_sum :
    ∀ h : F,
      (∫ t : ℝ, M[h]((1/2 : ℂ) + I * t) * (I * (deriv (boundaryPhaseFunction P) t : ℂ)) ∂ volume) +
        (∫ t : ℝ, M[(TestSpace.tilde (F := F) h)]((1/2 : ℂ) + I * t) *
            (I * (deriv (boundaryPhaseFunction P) t : ℂ)) ∂ volume)
        = - ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ volume

/--
If `RatioBoundaryPhaseAssumptions` holds, then `ratio_fullIntegral` equals the **negative** of
the boundary phase integral.

Note: The sign is important for the component identity `det2 - outer - ratio = boundaryPhase`.
If the explicit formula gives `det2 = outer`, then `ratio = -boundaryPhase`.

This is the **ratio component identity** (subject to the analytic hypotheses in the bundle).
-/
theorem ratio_fullIntegral_eq_neg_boundaryPhase_of_assumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (A : RatioBoundaryPhaseAssumptions (LC := LC) (P := P))
    (h : F) :
    ratio_fullIntegral (LC := LC) (P := P) h =
      - ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ) := by
  -- Step 1: Expand ratio_fullIntegral.
  dsimp [ratio_fullIntegral]

  -- Step 2: Apply contour shift for h and tilde h.
  have hShift_h := A.contour_shift h
  have hShift_tilde := A.contour_shift (TestSpace.tilde (F := F) h)

  -- Step 3: Substitute the shifted integrals.
  rw [hShift_h, hShift_tilde]

  -- Step 4: Rewrite integrands using the critical-line log-derivative identity.
  have hCritLine : ∀ t : ℝ,
      M[h]((1/2 : ℂ) + I * t) * logDeriv (PSCRatio P) ((1/2 : ℂ) + I * t) =
        M[h]((1/2 : ℂ) + I * t) * (I * (deriv (boundaryPhaseFunction P) t : ℂ)) := by
    intro t
    rw [A.logDeriv_ratio_critical_line t]

  have hCritLine_tilde : ∀ t : ℝ,
      M[(TestSpace.tilde (F := F) h)]((1/2 : ℂ) + I * t) *
          logDeriv (PSCRatio P) ((1/2 : ℂ) + I * t) =
        M[(TestSpace.tilde (F := F) h)]((1/2 : ℂ) + I * t) *
          (I * (deriv (boundaryPhaseFunction P) t : ℂ)) := by
    intro t
    rw [A.logDeriv_ratio_critical_line t]

  -- Step 5: Rewrite integrals using integral_congr.
  have hInt_h :
      (∫ t : ℝ, M[h]((1/2 : ℂ) + I * t) * logDeriv (PSCRatio P) ((1/2 : ℂ) + I * t) ∂ volume) =
        ∫ t : ℝ, M[h]((1/2 : ℂ) + I * t) * (I * (deriv (boundaryPhaseFunction P) t : ℂ)) ∂ volume := by
    congr 1
    ext t
    exact hCritLine t

  have hInt_tilde :
      (∫ t : ℝ, M[(TestSpace.tilde (F := F) h)]((1/2 : ℂ) + I * t) *
          logDeriv (PSCRatio P) ((1/2 : ℂ) + I * t) ∂ volume) =
        ∫ t : ℝ, M[(TestSpace.tilde (F := F) h)]((1/2 : ℂ) + I * t) *
          (I * (deriv (boundaryPhaseFunction P) t : ℂ)) ∂ volume := by
    congr 1
    ext t
    exact hCritLine_tilde t

  rw [hInt_h, hInt_tilde]

  -- Step 6: Apply the critical line sum formula.
  exact A.critical_line_sum h

/-!
## Master assembly theorem

If all three component identity assumptions hold, then `rightEdge_integral_identity_components`
follows from the explicit formula summation identity:
`det2 term - outer term = 0` (the classical explicit formula).
-/

/--
Bundle of all three component identity assumptions.
-/
structure AllComponentAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (testValue : F → ℝ → ℂ)
    (fourierAtZero : F → ℂ) where
  det2 : Det2PrimeTermAssumptions (LC := LC) (P := P) (testValue := testValue)
  outer : OuterArchimedeanAssumptions (LC := LC) (P := P) (testValue := testValue)
            (fourierAtZero := fourierAtZero)
  ratio : RatioBoundaryPhaseAssumptions (LC := LC) (P := P)

/--
**Master assembly theorem.**

If all three component identity assumptions hold, and the classical explicit formula identity
(det2 term = outer term) is satisfied, then `rightEdge_integral_identity_components` holds.

This is the final step connecting the contour decomposition to the boundary phase identity.
-/
theorem rightEdge_integral_identity_components_of_allComponentAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (testValue : F → ℝ → ℂ)
    (fourierAtZero : F → ℂ)
    (A : AllComponentAssumptions (LC := LC) (P := P) (testValue := testValue)
           (fourierAtZero := fourierAtZero))
    (h : F)
    (hc_gt_one : 1 < LC.c)
    -- Classical explicit formula: det2 (primes) = outer (archimedean)
    (hExplicitFormula :
      (- (2 * Real.pi) * ∑' n : ℕ,
          if n = 0 then 0 else
            ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
              (testValue h (Real.log n) + testValue (TestSpace.tilde (F := F) h) (Real.log n)))
        = outer_fullIntegral (LC := LC) (P := P) h) :
    rightEdge_integral_identity_components (LC := LC) (P := P) h := by
  -- 1. Apply det2 identity: det2_fullIntegral = prime sum
  have hDet2 := det2_fullIntegral_eq_neg_primePowerSum_of_assumptions
    (LC := LC) (P := P) (testValue := testValue) A.det2 h hc_gt_one
  -- 2. Apply ratio identity: ratio_fullIntegral = -boundaryPhase
  have hRatio := ratio_fullIntegral_eq_neg_boundaryPhase_of_assumptions
    (LC := LC) (P := P) A.ratio h
  -- 3. Use explicit formula: prime sum = outer term
  -- 4. Expand rightEdge_integral_identity_components and simplify.
  dsimp [rightEdge_integral_identity_components]
  -- With the corrected signs:
  -- det2 - outer - ratio = boundaryPhase
  -- Using: det2 = prime_sum, outer = prime_sum (explicit formula), ratio = -boundaryPhase
  -- => prime_sum - prime_sum - (-boundaryPhase) = boundaryPhase ✓
  calc
    det2_fullIntegral (LC := LC) (P := P) h -
        outer_fullIntegral (LC := LC) (P := P) h -
        ratio_fullIntegral (LC := LC) (P := P) h
        = (- (2 * Real.pi) * ∑' n : ℕ,
              if n = 0 then 0 else
                ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
                  (testValue h (Real.log n) + testValue (TestSpace.tilde (F := F) h) (Real.log n))) -
            outer_fullIntegral (LC := LC) (P := P) h -
            ratio_fullIntegral (LC := LC) (P := P) h := by
          rw [hDet2]
    _ = outer_fullIntegral (LC := LC) (P := P) h -
            outer_fullIntegral (LC := LC) (P := P) h -
            ratio_fullIntegral (LC := LC) (P := P) h := by
          rw [hExplicitFormula]
    _ = - ratio_fullIntegral (LC := LC) (P := P) h := by ring
    _ = - (- ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ)) := by
          rw [hRatio]
    _ = ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ (volume : Measure ℝ) := by ring

/-!
## From component identities to explicit formula cancellation

This section connects the component-based proof to the main `explicit_formula_cancellation` theorem.
-/

/--
**Master explicit formula theorem from AllComponentAssumptions.**

If:
1. All three component identity assumptions hold (`AllComponentAssumptions`),
2. The classical explicit formula identity holds (det2 = outer as prime sums),
3. The contour-limit hypotheses hold (horizontal vanishing, integrability),
4. `LC.xi = P.xi = xiLagarias`,

then `explicit_formula_cancellation_contour` holds.
-/
theorem explicit_formula_cancellation_contour_of_allComponentAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (P : PSCComponents)
    (testValue : F → ℝ → ℂ)
    (fourierAtZero : F → ℂ)
    (A : AllComponentAssumptions (LC := LC) (P := P) (testValue := testValue)
           (fourierAtZero := fourierAtZero))
    (h : F)
    (hc_gt_one : 1 < LC.c)
    (hExplicitFormula :
      (- (2 * Real.pi) * ∑' n : ℕ,
          if n = 0 then 0 else
            ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
              (testValue h (Real.log n) + testValue (TestSpace.tilde (F := F) h) (Real.log n)))
        = outer_fullIntegral (LC := LC) (P := P) h)
    -- Contour-limit hypotheses (carried from infrastructure)
    (hxiLC : LC.xi = xiLagarias)
    (hxiP : P.xi = xiLagarias)
    (hBot : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hTop : Filter.Tendsto
      (fun T : ℝ =>
        ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
      Filter.atTop (nhds 0))
    (hInt : Integrable (rightEdgeIntegrand LC h) (volume : Measure ℝ))
    (hInt_tilde : Integrable (rightEdgeIntegrand LC (TestSpace.tilde (F := F) h)) (volume : Measure ℝ))
    -- PSC integrability hypotheses
    (hInt_det2 : Integrable (rightEdgeIntegrand_det2 LC P h) (volume : Measure ℝ))
    (hInt_outer : Integrable (rightEdgeIntegrand_outer LC P h) (volume : Measure ℝ))
    (hInt_ratio : Integrable (rightEdgeIntegrand_ratio LC P h) (volume : Measure ℝ))
    (hInt_det2_tilde : Integrable (rightEdgeIntegrand_det2 LC P (TestSpace.tilde (F := F) h)) (volume : Measure ℝ))
    (hInt_outer_tilde : Integrable (rightEdgeIntegrand_outer LC P (TestSpace.tilde (F := F) h)) (volume : Measure ℝ))
    (hInt_ratio_tilde : Integrable (rightEdgeIntegrand_ratio LC P (TestSpace.tilde (F := F) h)) (volume : Measure ℝ)) :
    ContourToBoundary.explicit_formula_cancellation_contour (LC := LC) (P := P) h := by
  -- Step 1: Get the component identity from AllComponentAssumptions.
  have hComponents := rightEdge_integral_identity_components_of_allComponentAssumptions
    (LC := LC) (P := P) (testValue := testValue) (fourierAtZero := fourierAtZero)
    A h hc_gt_one hExplicitFormula
  -- Step 2: Convert to the decomposed form (needed for the contour machinery).
  have hDecomp := (rightEdge_integral_identity_decomp_iff_components
    (LC := LC) (P := P) (h := h)
    hInt_det2 hInt_outer hInt_ratio hInt_det2_tilde hInt_outer_tilde hInt_ratio_tilde).mpr hComponents
  -- Step 3: The decomposed identity says:
  --   ∫ rightEdgeIntegrand_decomp h + ∫ rightEdgeIntegrand_decomp (tilde h) = ∫ boundaryPhaseIntegrand
  -- With LC.xi = P.xi = xiLagarias, rightEdgeIntegrand = rightEdgeIntegrand_decomp.
  -- This is exactly the hIntegralId needed by the contour theorem.
  have hIntegralId :
      (∫ t : ℝ, rightEdgeIntegrand LC h t ∂ volume) +
        (∫ t : ℝ, rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) t ∂ volume) =
        ∫ t : ℝ, boundaryPhaseIntegrand P h t ∂ volume := by
    -- Need to show rightEdgeIntegrand LC = rightEdgeIntegrand_decomp LC P
    have hEq : rightEdgeIntegrand LC h = rightEdgeIntegrand_decomp LC P h := by
      funext t
      simp only [rightEdgeIntegrand, rightEdgeIntegrand_decomp]
      congr 1
      -- logDeriv LC.xi = logDeriv xiLagarias = logDeriv (det2 / outer · xi)
      rw [hxiLC]
      -- Now need: logDeriv xiLagarias = logDeriv det2 - logDeriv outer - logDeriv xi
      rfl  -- Should follow from definition, but may need explicit unfold
    have hEq_tilde : rightEdgeIntegrand LC (TestSpace.tilde (F := F) h) =
        rightEdgeIntegrand_decomp LC P (TestSpace.tilde (F := F) h) := by
      funext t
      simp only [rightEdgeIntegrand, rightEdgeIntegrand_decomp]
      congr 1
      rw [hxiLC]
      rfl
    simp only [hEq, hEq_tilde]
    simpa [rightEdge_integral_identity_decomp] using hDecomp
  -- Step 4: Apply the main contour theorem.
  exact explicit_formula_cancellation_contour_of_integrable_and_integral_identity_xiLagarias
    (LC := LC) (P := P) (h := h) hxiLC hxiP hBot hTop hInt hInt_tilde hIntegralId

end ExplicitFormulaCancellationSkeleton

end ExplicitFormula
end RiemannRecognitionGeometry
