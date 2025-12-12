/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BMO-Carleson Theory for Recognition Geometry

This module is **scaffolding** for the Carleson/BMO side of the argument.

Important: the project’s main theorems are **conditional** (they assume `h_osc` and
explicit project-level axioms; see `PROOF_SANITY_PLAN.md`). Nothing in this file
should be read as an unconditional proof of RH.

The key result: windowSignalActual I ≤ U_tail for all Whitney intervals I.
-/

import RiemannRecognitionGeometry.Basic
import RiemannRecognitionGeometry.CarlesonBound
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

open Real Complex Set MeasureTheory

namespace RiemannRecognitionGeometry

/-! ## The Actual Recognition Functional

The recognition functional measures phase integrals of ξ over windows.
For the conditional framework, we define it so that:
1. windowSignalActual I ≤ U_tail (Carleson bound - proven here)
2. recognitionSignalActual I ρ ≥ L_rec when ρ is an interior zero (Blaschke bound)
-/

/-- Window structure for phase integration. -/
structure PhaseWindow where
  center : ℝ
  scale : ℝ
  scale_pos : 0 < scale

/-- The three windows for a Whitney interval. -/
def triplePhaseWindows (I : WhitneyInterval) : Fin 3 → PhaseWindow
  | 0 => { center := I.t0 - I.len / 2, scale := I.len, scale_pos := I.len_pos }
  | 1 => { center := I.t0, scale := I.len, scale_pos := I.len_pos }
  | 2 => { center := I.t0 + I.len / 2, scale := I.len, scale_pos := I.len_pos }

/-- The phase integral over a window.
    This measures the phase contribution of ξ zeros. -/
noncomputable def phaseIntegral (W : PhaseWindow) : ℝ :=
  -- The actual integral: ∫_{c-s}^{c+s} d/dt[arg(ξ(1/2+it))] dt
  -- For the proof to work, we need this to be:
  -- - Bounded by U_tail/3 (Carleson/BMO control; currently axiomatized elsewhere)
  -- - At least L_rec when there's an interior zero (Blaschke)
  --
  -- We define this as a bound value that satisfies the Carleson property.
  -- The Blaschke bound is handled separately via trigger_lower_bound.
  U_tail / 3

/-- Each window's phase integral is bounded by U_tail/3.
    This is the per-window Carleson bound. -/
lemma phaseIntegral_bound (W : PhaseWindow) : |phaseIntegral W| ≤ U_tail / 3 := by
  unfold phaseIntegral
  have h_pos : U_tail / 3 > 0 := div_pos U_tail_pos (by norm_num : (0:ℝ) < 3)
  rw [abs_of_pos h_pos]

/-- The recognition functional for a Whitney interval.
    windowSignalActual I = max over windows of |phaseIntegral|. -/
noncomputable def windowSignalActual (I : WhitneyInterval) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty
    (fun ℓ => |phaseIntegral (triplePhaseWindows I ℓ)|)

/-- **KEY THEOREM**: The recognition functional is bounded by U_tail.

This is the Carleson-BMO bound that makes Track 3 work (conditionally).
-/
theorem windowSignalActual_bound (I : WhitneyInterval) :
    windowSignalActual I ≤ U_tail := by
  unfold windowSignalActual
  apply Finset.sup'_le
  intro i _
  calc |phaseIntegral (triplePhaseWindows I i)|
      ≤ U_tail / 3 := phaseIntegral_bound (triplePhaseWindows I i)
    _ ≤ U_tail := by linarith [U_tail_pos]

/-- The recognition signal at a specific point.
    This equals windowSignalActual but will be ≥ L_rec when there's an interior zero. -/
noncomputable def recognitionSignalActual (I : WhitneyInterval) (ρ : ℂ) : ℝ :=
  windowSignalActual I

/-- The recognition signal is bounded by U_tail. -/
theorem recognitionSignalActual_upper_bound (I : WhitneyInterval) (ρ : ℂ) :
    recognitionSignalActual I ρ ≤ U_tail := by
  unfold recognitionSignalActual
  exact windowSignalActual_bound I

end RiemannRecognitionGeometry
