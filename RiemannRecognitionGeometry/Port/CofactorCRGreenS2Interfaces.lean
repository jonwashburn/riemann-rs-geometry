import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RiemannRecognitionGeometry.Port.CofactorCRGreenAssumptions
import RiemannRecognitionGeometry.Port.RealPhaseTransfer
import RiemannRecognitionGeometry.Phase

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex MeasureTheory

namespace CofactorCRGreenS2Interfaces

open Filter

/-!
# Port scaffold: minimal analytic interfaces for the S2-only CR/Green wall

We have reduced the RG CR/Green bottleneck to the **strong** energy-form statement
`Port.CofactorCRGreenAssumptionsStrong`:

`‖Δθ_cofactor(I,ρ)‖ ≤ sqrt(Ebox(I,ρ)) * (C_geom * |I|^{-1/2})`.

This file decomposes that bound into the two standard analytic steps one expects from a faithful proof:

1. **Green trace identity + boundary-term gate**:
   represent `Δθ_real(I,ρ)` as an integral of a (measurable/integrable) phase-velocity density.
2. **Cauchy–Schwarz pairing bound**:
   bound that boundary pairing by `sqrt(Ebox) * (C_geom * |I|^{-1/2})`.

The intent is to let us swap in actual proofs piece-by-piece:
first prove the trace identity (often the hardest bookkeeping, including boundary terms / traces),
then prove the pairing bound (often a clean C–S + window-energy computation).
-/

/-!
### Optional finer split of the S2a trace gate (for “smallest lemma” chipping)

`GreenTraceIdentity` bundles two logically distinct ingredients:

1. a **phase lift** `θ` on the Whitney base (a real-valued representative whose coercion to
   `Real.Angle` matches `rgCofactorPhaseAngle`), and
2. an **FTC-valid phase velocity** `dθ/dt` for that lift on the Whitney base.

When chasing the minimal missing lemma, it is often helpful to name these separately.
The bundled `GreenTraceIdentity` can be rebuilt from the two subgates via
`GreenTraceIdentity.of_lift_and_ftc`.
-/

/-- Subgate S2a0: existence of a real-valued lift of the cofactor `Real.Angle` phase on Whitney bases. -/
structure CofactorPhaseLift where
  theta : WhitneyInterval → ℂ → (ℝ → ℝ)
  coe_theta_eq :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (t : ℝ),
      t ∈ I.interval → (theta I ρ t : Real.Angle) = rgCofactorPhaseAngle ρ t

/-- Subgate S2a1: given a phase lift, it has an FTC-valid (integrable) velocity density on Whitney bases. -/
structure PhaseVelocityFTC (L : CofactorPhaseLift) where
  dPhase : WhitneyInterval → ℂ → (ℝ → ℝ)
  hasDerivAt :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (t : ℝ),
      t ∈ Set.uIcc (I.t0 - I.len) (I.t0 + I.len) →
        HasDerivAt (fun u => L.theta I ρ u) (dPhase I ρ t) t
  intervalIntegrable :
    ∀ (I : WhitneyInterval) (ρ : ℂ),
      IntervalIntegrable (fun t => dPhase I ρ t) volume (I.t0 - I.len) (I.t0 + I.len)

/-- Subgate S2a1-BT: the phase velocity is a genuine *boundary trace* of a 2D field.

This is the “boundary-term gate” that typically comes from a Green/Cauchy–Riemann computation:
`θ'(t)` is identified with (a component of) the boundary trace of a harmonic/Dirichlet gradient.

We do **not** commit to a particular PDE model here; we only record the existence of a field
whose boundary trace equals the phase velocity. -/
structure PhaseVelocityBoundaryTrace (L : CofactorPhaseLift) (F : PhaseVelocityFTC L) where
  gradField : WhitneyInterval → ℂ → (ℝ × ℝ → ℝ × ℝ)
  trace_eq :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (t : ℝ),
      t ∈ Set.uIcc (I.t0 - I.len) (I.t0 + I.len) →
        F.dPhase I ρ t = (gradField I ρ (t, 0)).1

/-- Subgate S2a1-BT-Poisson (non-vacuous): the phase velocity is the **boundary limit**
of the x-derivative of the conjugate Poisson extension of `cofactorLogAbs ρ`.

This ties the boundary-term gate to the same Poisson-model field whose Carleson-box energy defines
`cofactorEbox_poisson`. -/
structure PhaseVelocityBoundaryTracePoisson (L : CofactorPhaseLift) (F : PhaseVelocityFTC L) : Prop where
  /-- As `y → 0⁺`, the x-component of `∇(conjugate Poisson)[cofactorLogAbs ρ] (t,y)` tends to
  the phase velocity `θ'(t)`. -/
  tendsto_dx_conjPoisson :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (t : ℝ),
      t ∈ Set.uIcc (I.t0 - I.len) (I.t0 + I.len) →
        Tendsto
          (fun y : ℝ =>
            (PoissonExtension.gradient_conjugate_poisson (cofactorLogAbs ρ) (t, y)).1)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (F.dPhase I ρ t))

/-- Subgate A (S2a): an **FTC/trace gate** for the default real phase representative.

The key honesty point: we do **not** differentiate `argXi` (principal branch), which is not a faithful
phase function. Instead we introduce a real-valued phase *lift* `θ` whose coercion to `Real.Angle`
agrees with `rgCofactorPhaseAngle` on the Whitney base, and we require `θ` to have a genuine
derivative density `dPhase` suitable for the FTC.

In a faithful CR/Green proof, `dPhase` is identified with a boundary trace of a harmonic/Dirichlet
field (e.g. `-∂y U(t,0)`), and this is where “boundary-term gates” live. -/
structure GreenTraceIdentity where
  /-- A real-valued phase lift for the cofactor `Real.Angle` phase on the Whitney base. -/
  theta : WhitneyInterval → ℂ → (ℝ → ℝ)

  /-- The lift agrees with the cofactor `Real.Angle` phase on the Whitney base interval. -/
  coe_theta_eq :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (t : ℝ),
      t ∈ I.interval → (theta I ρ t : Real.Angle) = rgCofactorPhaseAngle ρ t

  /-- A candidate phase-velocity density `dθ/dt` for the lift on the Whitney base. -/
  dPhase : WhitneyInterval → ℂ → (ℝ → ℝ)

  /-- Pointwise derivative identification on the Whitney base interval (in the `HasDerivAt` sense). -/
  hasDerivAt :
    ∀ (I : WhitneyInterval) (ρ : ℂ) (t : ℝ),
      t ∈ Set.uIcc (I.t0 - I.len) (I.t0 + I.len) →
        HasDerivAt (fun u => theta I ρ u) (dPhase I ρ t) t

  /-- Interval-integrability of the phase-velocity density on the Whitney base. -/
  intervalIntegrable :
    ∀ (I : WhitneyInterval) (ρ : ℂ),
      IntervalIntegrable (fun t => dPhase I ρ t) volume (I.t0 - I.len) (I.t0 + I.len)

namespace GreenTraceIdentity

/-- Build the bundled trace gate from the two finer S2a subgates. -/
def of_lift_and_ftc (L : CofactorPhaseLift) (F : PhaseVelocityFTC L) : GreenTraceIdentity where
  theta := L.theta
  coe_theta_eq := L.coe_theta_eq
  dPhase := F.dPhase
  hasDerivAt := F.hasDerivAt
  intervalIntegrable := F.intervalIntegrable

/-- The real phase change of the lift across the Whitney base. -/
def phaseChangeReal (T : GreenTraceIdentity) (I : WhitneyInterval) (ρ : ℂ) : ℝ :=
  T.theta I ρ (I.t0 + I.len) - T.theta I ρ (I.t0 - I.len)

/-- The lift phase change, coerced to `Real.Angle`, recovers the true cofactor `Real.Angle` phase
difference on the Whitney base. -/
lemma coe_phaseChangeReal (T : GreenTraceIdentity) (I : WhitneyInterval) (ρ : ℂ) :
    (phaseChangeReal T I ρ : Real.Angle) =
      rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len) := by
  have ha : (I.t0 - I.len) ∈ I.interval := by
    refine ⟨?_, ?_⟩ <;> linarith [I.len_pos]
  have hb : (I.t0 + I.len) ∈ I.interval := by
    refine ⟨?_, ?_⟩ <;> linarith [I.len_pos]
  have hθa : (T.theta I ρ (I.t0 - I.len) : Real.Angle) = rgCofactorPhaseAngle ρ (I.t0 - I.len) :=
    T.coe_theta_eq I ρ (I.t0 - I.len) ha
  have hθb : (T.theta I ρ (I.t0 + I.len) : Real.Angle) = rgCofactorPhaseAngle ρ (I.t0 + I.len) :=
    T.coe_theta_eq I ρ (I.t0 + I.len) hb
  -- Convert the real difference to a `Real.Angle` difference.
  unfold phaseChangeReal
  -- `((x - y : ℝ) : Real.Angle) = (x : Real.Angle) - (y : Real.Angle)`.
  simpa [Real.Angle.coe_sub, hθa, hθb]

/-- The fundamental theorem of calculus turns `HasDerivAt`+integrability into the desired
trace identity `Δθ = ∫ dPhase`. -/
lemma phaseChange_eq_intervalIntegral (T : GreenTraceIdentity) (I : WhitneyInterval) (ρ : ℂ) :
    phaseChangeReal T I ρ =
      ∫ t in (I.t0 - I.len)..(I.t0 + I.len), T.dPhase I ρ t := by
  classical
  -- Shorthand for endpoints.
  set a : ℝ := I.t0 - I.len
  set b : ℝ := I.t0 + I.len
  have hderiv :
      ∀ t ∈ Set.uIcc a b,
        HasDerivAt (fun u => T.theta I ρ u) (T.dPhase I ρ t) t := by
    intro t ht
    exact T.hasDerivAt I ρ t (by simpa [a, b] using ht)
  have hint : IntervalIntegrable (fun t => T.dPhase I ρ t) volume a b := by
    simpa [a, b] using T.intervalIntegrable I ρ
  have hftc :
      (∫ t in a..b, T.dPhase I ρ t) =
        T.theta I ρ b - T.theta I ρ a := by
    simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint)
  -- Rewrite `Δθ_real_default` as `F(b)-F(a)` and flip the FTC equality.
  simpa [phaseChangeReal, a, b] using hftc.symm

end GreenTraceIdentity

/-- Subgate B: CR/Green pairing bound for the trace integrand.

This is the Cauchy–Schwarz output: the boundary pairing is controlled by the square-root
of the box energy, times the fixed window scaling constant `C_geom * |I|^{-1/2}`. -/
structure PairingBound (T : GreenTraceIdentity) : Prop where
  bound :
    ∀ (I : WhitneyInterval) (ρ : ℂ),
      |∫ t in (I.t0 - I.len)..(I.t0 + I.len), T.dPhase I ρ t|
        ≤ Real.sqrt (cofactorEbox_poisson ρ I) * (C_geom * (1 / Real.sqrt (2 * I.len)))

/-- Green trace identity + pairing bound ⇒ the **strong** cofactor CR/Green bound. -/
theorem cofactorCRGreenAssumptionsStrong_of_greenTrace_and_pairing
    (T : GreenTraceIdentity) (hB : PairingBound T) :
    CofactorCRGreenAssumptionsStrong := by
  refine ⟨?_⟩
  intro I ρ
  -- Let `Δθ_real := θ(b) - θ(a)` for the chosen lift.
  have hFTC :
      GreenTraceIdentity.phaseChangeReal T I ρ =
        ∫ t in (I.t0 - I.len)..(I.t0 + I.len), T.dPhase I ρ t :=
    GreenTraceIdentity.phaseChange_eq_intervalIntegral T I ρ
  have hAbs :
      |GreenTraceIdentity.phaseChangeReal T I ρ| ≤
        Real.sqrt (cofactorEbox_poisson ρ I) * (C_geom * (1 / Real.sqrt (2 * I.len))) := by
    -- rewrite via FTC and use the pairing bound
    simpa [hFTC] using (hB.bound I ρ)
  -- The angle difference is the coercion of the lift phase change.
  have hcoe :
      (GreenTraceIdentity.phaseChangeReal T I ρ : Real.Angle) =
        rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len) :=
    GreenTraceIdentity.coe_phaseChangeReal T I ρ
  -- Control the `Real.Angle` norm by the abs of the real representative.
  have hnorm :
      ‖rgCofactorPhaseAngle ρ (I.t0 + I.len) - rgCofactorPhaseAngle ρ (I.t0 - I.len)‖ ≤
        |GreenTraceIdentity.phaseChangeReal T I ρ| := by
    -- `‖angleDiff‖ = ‖(Δθ_real : Real.Angle)‖ ≤ |Δθ_real|`.
    have := realAngle_norm_coe_le_abs (GreenTraceIdentity.phaseChangeReal T I ρ)
    -- rewrite the LHS using `hcoe`
    simpa [hcoe] using this
  -- Chain.
  have hAbs' :
      |GreenTraceIdentity.phaseChangeReal T I ρ| ≤
        C_geom * Real.sqrt (cofactorEbox_poisson ρ I) * (1 / Real.sqrt (2 * I.len)) := by
    -- rearrange the RHS of `hAbs` (commutativity/associativity only)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hAbs
  exact le_trans hnorm hAbs'

end CofactorCRGreenS2Interfaces

end Port
end RiemannRecognitionGeometry
