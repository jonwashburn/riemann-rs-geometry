/-
# Li coefficients and Li criterion (Route 3 skeleton)

This file records (as Lean-typed statements) the Li-criterion gate for RH and
its relationship to the explicit-formula/Weil gate.

Analytic convergence and the “sum over zeros” identity are intentionally
packaged as assumptions.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace

/--
A Li-criterion package (Li 1997; Lagarias 2007, Thm 6.5), layered on top of a
Lagarias explicit-formula framework.

We take Li coefficients `λ n` as real numbers (as in the criterion), and record
`RH ↔ (∀n≥1, λ n ≥ 0)`.

Further identities (sum over zeros, and the Bombieri–Lagarias realization as a
Weil functional) are represented as explicit fields, but kept abstract.
-/
structure LiFramework (F : Type) [TestSpace F] extends LagariasFramework F where
  /-- Li coefficients `λₙ` (real). -/
  lambda : ℕ → ℝ

  /-- Li criterion (Lagarias 2007, Thm 6.5): `RH ↔ ∀ n≥1, λₙ ≥ 0`. -/
  liCriterion : RiemannHypothesis ↔ (∀ n : ℕ, 1 ≤ n → 0 ≤ lambda n)

  /-- Optional: record the (symmetric) sum-over-zeros formula as a named assumption. -/
  sumOverZerosFormula : Prop

  /-- Optional: record the Bombieri–Lagarias/Lagarias realization `λₙ = W¹(φₙ * \widetilde{\bar φₙ})`.
      This typically requires extending the test-function class beyond compact support. -/
  lambdaAsWeil : Prop

namespace LiFramework

variable {F : Type} [TestSpace F] (L : LiFramework F)

/-- `LiGate`: the countable positivity hypothesis `∀ n≥1, λₙ ≥ 0`. -/
def LiGate : Prop := ∀ n : ℕ, 1 ≤ n → 0 ≤ L.lambda n

end LiFramework

end ExplicitFormula
end RiemannRecognitionGeometry

