/-
Faithful phase interface for Recognition Geometry.

Motivation:
The principal argument `Complex.arg : ℂ → ℝ` is discontinuous (branch cut), so treating
`argXi(t)` as a globally well-behaved harmonic conjugate is not faithful.

A standard way to model phase correctly is to work modulo `2π`, i.e. in `Real.Angle = ℝ/2πℤ`.
On intervals where ξ is nonzero, one can (in analysis) lift this to a continuous real-valued phase;
later milestones will add the needed hypotheses/lemmas for such lifts.
-/

import RiemannRecognitionGeometry.FeffermanStein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Normed.Group.AddCircle

noncomputable section

open Real Complex

namespace RiemannRecognitionGeometry

/-- Phase of ξ on the critical line as an element of `Real.Angle = ℝ/2πℤ`.

This is the argument **modulo 2π**, so branch cut jumps of `Complex.arg` are identified.
At zeros we still take the junk value coming from `arg 0 = 0`.
-/
def phaseXi (t : ℝ) : Real.Angle :=
  ((xiOnCriticalLine t).arg : Real.Angle)

/-- Phase change across a Whitney interval, valued in `Real.Angle` (i.e. modulo `2π`). -/
def xiPhaseChangeAngle (I : WhitneyInterval) : Real.Angle :=
  phaseXi (I.t0 + I.len) - phaseXi (I.t0 - I.len)

/-- A real-valued size of phase change: the norm on `Real.Angle`.

This is the shortest-distance representative in `[-π, π]`.
-/
def xiPhaseChange (I : WhitneyInterval) : ℝ :=
  ‖xiPhaseChangeAngle I‖

/-- Any angle has norm ≤ π. In particular, `xiPhaseChange I ≤ π`. -/
lemma xiPhaseChange_le_pi (I : WhitneyInterval) : xiPhaseChange I ≤ Real.pi := by
  -- General bound: for `AddCircle p`, ‖x‖ ≤ |p|/2.
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by
    nlinarith [Real.pi_pos]
  have h := (AddCircle.norm_le_half_period (p := (2 * Real.pi)) (x := xiPhaseChangeAngle I) hp)
  have hRHS : |(2 * Real.pi : ℝ)| / 2 = Real.pi := by
    have hpos : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    calc
      |(2 * Real.pi : ℝ)| / 2 = (2 * Real.pi) / 2 := by simp [abs_of_pos hpos]
      _ = Real.pi := by
            -- rewrite as `π * 2 / 2`
            simpa [mul_comm] using
              (mul_div_cancel_left₀ (Real.pi) (2 : ℝ) (two_ne_zero : (2 : ℝ) ≠ 0))
  -- `xiPhaseChange I = ‖xiPhaseChangeAngle I‖`.
  simpa [xiPhaseChange, hRHS] using h

end RiemannRecognitionGeometry
