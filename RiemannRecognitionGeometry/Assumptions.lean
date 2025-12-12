/-
Bundled assumptions used by the main theorems.

Goal: make dependencies explicit at the theorem signatures.

We separate:
- **Classical analysis assumptions** (expected true in standard analysis): e.g. Green/Cauchy–Schwarz.
- **RG-specific assumptions** (the bottleneck estimate(s) of the Recognition Geometry approach): e.g. the
  Weierstrass/Hadamard tail bound.

This file is intentionally lightweight: it packages existing statement-shapes without changing any proofs.
-/

import RiemannRecognitionGeometry.Conjectures
import RiemannRecognitionGeometry.DirichletEta

noncomputable section

open Real Complex Set MeasureTheory

namespace RiemannRecognitionGeometry

/-- Classical analysis assumptions used by the RG main chain. -/
structure ClassicalAnalysisAssumptions : Prop where
  /-- Green–Cauchy–Schwarz (phase change bounded by Carleson energy). -/
  green_identity_axiom_statement :
    ∀ (J : WhitneyInterval) (C : ℝ) (hC_pos : C > 0)
      (hC_le : C ≤ K_tail) (M : ℝ) (hM_pos : M > 0) (hM_le : M ≤ C),
      xiPhaseChange J ≤
        C_geom * Real.sqrt (M * (2 * J.len)) * (1 / Real.sqrt (2 * J.len))

  /-- ζ(s) ≠ 0 for real `s ∈ (0, 1)`. (Used to rule out real zeros when `Im ρ = 0`.) -/
  zeta_ne_zero_of_real_in_unit_interval :
    ∀ s : ℝ, 0 < s → s < 1 → riemannZeta (s : ℂ) ≠ 0

/-- RG-specific bottleneck assumptions (not known to be true unconditionally). -/
structure RGAssumptions : Prop where
  /-- Weierstrass/Hadamard tail bound: isolate a zero’s Blaschke contribution and bound the remainder. -/
  weierstrass_tail_bound_axiom_statement :
    ∀ (I : WhitneyInterval) (ρ : ℂ),
      completedRiemannZeta ρ = 0 → ρ.im ∈ I.interval →
      let d : ℝ := ρ.re - 1/2
      let y_hi : ℝ := I.t0 + I.len - ρ.im
      let y_lo : ℝ := I.t0 - I.len - ρ.im
      let blaschke := Real.arctan (y_lo / d) - Real.arctan (y_hi / d)
      ‖xiPhaseChangeAngle I - (blaschke : Real.Angle)‖ ≤ U_tail

namespace Assumptions

/-- Convenience: build `ClassicalAnalysisAssumptions` from the current axiom registry in `Conjectures.lean`. -/
def classicalFromAxioms : ClassicalAnalysisAssumptions :=
  ⟨Conjectures.green_identity_axiom_statement, fun s hs_pos hs_lt =>
    riemannZeta_ne_zero_of_pos_lt_one s hs_pos hs_lt⟩

/-- Convenience: build `RGAssumptions` from the current axiom registry in `Conjectures.lean`. -/
def rgFromAxioms : RGAssumptions :=
  ⟨Conjectures.weierstrass_tail_bound_axiom_statement⟩

end Assumptions

end RiemannRecognitionGeometry
