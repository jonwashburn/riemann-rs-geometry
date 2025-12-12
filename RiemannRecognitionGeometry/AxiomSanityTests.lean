/-
Axiom sanity tests (guardrails).

These lemmas are **not** mathematical proofs of the project axioms.
They are small checks that the *statement shapes* behave sensibly on trivial inputs
(e.g. the zero function), and that the main numeric constants are compatible with
basic bounds (e.g. `xiPhaseChange ≤ π`).
-/

import RiemannRecognitionGeometry.Conjectures
import RiemannRecognitionGeometry.PoissonExtension
import Mathlib.MeasureTheory.Integral.SetIntegral

noncomputable section

open Real Complex Set MeasureTheory
open scoped BigOperators MeasureTheory

namespace RiemannRecognitionGeometry

namespace AxiomSanityTests

open RiemannRecognitionGeometry.PoissonExtension

/-! ## Poisson/Carleson sanity checks -/

lemma gradient_conjugate_poisson_zero (z : ℝ × ℝ) :
    PoissonExtension.gradient_conjugate_poisson (fun _ : ℝ => 0) z = (0, 0) := by
  simp [PoissonExtension.gradient_conjugate_poisson, PoissonExtension.conjugate_poisson_integral]

lemma carleson_energy_zero (a b : ℝ) :
    PoissonExtension.carleson_energy (fun _ : ℝ => 0) a b = 0 := by
  simp [PoissonExtension.carleson_energy, gradient_conjugate_poisson_zero]

/-- The BMO→Carleson axiom is compatible with the zero function. -/
lemma bmo_carleson_embedding_zero (a b M : ℝ) (hM_pos : M > 0) :
    PoissonExtension.carleson_energy (fun _ : ℝ => 0) a b ≤ C_FS * M ^ 2 * (b - a) := by
  -- Provide the (trivial) BMO hypothesis for `w := 0`.
  refine
    PoissonExtension.bmo_carleson_embedding (w := fun _ : ℝ => 0) (a := a) (b := b) (M := M)
      hM_pos ?_
  intro a' b' hab
  -- The left side is definitionaly `0` for the zero function.
  have : (0 : ℝ) ≤ M := le_of_lt hM_pos
  simpa using this

/-! ## Phase axiom shape checks -/

/-- Instantiating the Green-identity axiom at `C = M = K_tail` yields the uniform bound
`xiPhaseChange J ≤ U_tail`.

This is the intended “phase is controlled by the Carleson constant” consequence.
-/
lemma green_identity_gives_U_tail (J : WhitneyInterval) : xiPhaseChange J ≤ U_tail := by
  have h :=
    Conjectures.green_identity_axiom_statement J K_tail K_tail_pos (le_rfl : K_tail ≤ K_tail)
      K_tail K_tail_pos (le_rfl : K_tail ≤ K_tail)
  -- Cancel the interval-length normalization.
  have h_cancel :
      Real.sqrt (K_tail * (2 * J.len)) * (1 / Real.sqrt (2 * J.len)) = Real.sqrt K_tail := by
    have hK : 0 ≤ K_tail := le_of_lt K_tail_pos
    have hL : 0 < (2 * J.len) := by nlinarith [J.len_pos]
    simpa using (sqrt_energy_cancellation K_tail (2 * J.len) hK hL)
  have h1 := h
  rw [mul_assoc] at h1
  rw [h_cancel] at h1
  simpa [U_tail] using h1

/-- Numeric sanity: the main upper bound `U_tail` is strictly less than `π`.

This ensures a uniform bound like `xiPhaseChange ≤ U_tail` is compatible with the universal
angle-norm bound `xiPhaseChange ≤ π`.
-/
lemma U_tail_lt_pi : U_tail < Real.pi := by
  -- `U_tail = (1/2) * √2.1 < 0.75 < 3 < π`.
  have h_pi : 3 < Real.pi := Real.pi_gt_three
  have h_sqrt : Real.sqrt 2.1 < (1.5 : ℝ) := sqrt_21_lt
  have h_utail : U_tail < (0.75 : ℝ) := by
    unfold U_tail C_geom K_tail
    nlinarith [h_sqrt]
  have h075_lt_3 : (0.75 : ℝ) < 3 := by norm_num
  linarith

end AxiomSanityTests

end RiemannRecognitionGeometry
