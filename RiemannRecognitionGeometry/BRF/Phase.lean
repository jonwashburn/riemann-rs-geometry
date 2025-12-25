/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BRF Route: Phase Function

Ported from: reality/IndisputableMonolith/NumberTheory/RiemannHypothesis/Wedge.lean (lines 25-27)

Defines the unimodular phase function `e^{iw}` used in the boundary wedge analysis.
-/

import Mathlib

namespace RiemannRecognitionGeometry
namespace BRF

open scoped Real

/-- The unimodular complex number with phase `w`: `e^{i w}`. -/
noncomputable def phase (w : ℝ) : ℂ :=
  Complex.exp (w * Complex.I)

/-- The phase function has unit modulus. -/
theorem abs_phase (w : ℝ) : Complex.abs (phase w) = 1 := by
  simp [phase, Complex.abs_exp]

end BRF
end RiemannRecognitionGeometry
