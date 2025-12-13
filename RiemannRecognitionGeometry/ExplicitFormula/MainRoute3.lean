/-
# Route 3 main file: explicit-formula gates → RH

This file exposes the Route 3 “gate” theorems:

- `WeilGate → RiemannHypothesis`
- `LiGate → RiemannHypothesis`

All analytic number theory content is isolated behind the Lagarias/Li framework
assumptions; this is a mechanically checkable proof *skeleton*.

Important non-goal (Conrey–Li): we do **not** target de Branges shift-positivity
(pointwise kernel-shift inequalities), which are known to fail for ζ.
The positivity target here is Weil/Li *averaged* positivity.
-/

import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.Li

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace

namespace LagariasFramework

variable {F : Type} [TestSpace F] (L : LagariasFramework F)

/-- Route 3 Weil gate: assuming the Weil positivity hypothesis yields RH. -/
theorem WeilGate_implies_RH : L.WeilGate → RiemannHypothesis := by
  intro hGate
  exact (L.weilPositivity).2 hGate

/-- Under RH, Weil positivity holds (the easy direction of Lagarias Thm 3.2). -/
theorem RH_implies_WeilGate : RiemannHypothesis → L.WeilGate := by
  intro hRH
  exact (L.weilPositivity).1 hRH

end LagariasFramework

namespace LiFramework

variable {F : Type} [TestSpace F] (L : LiFramework F)

/-- Route 3 Li gate: assuming Li-positivity yields RH. -/
theorem LiGate_implies_RH : L.LiGate → RiemannHypothesis := by
  intro hGate
  exact (L.liCriterion).2 hGate

/-- Under RH, Li positivity holds (the easy direction of Li's criterion). -/
theorem RH_implies_LiGate : RiemannHypothesis → L.LiGate := by
  intro hRH
  exact (L.liCriterion).1 hRH

end LiFramework

/-
## Optional intermediate targets (“attackability”)

These are **not** needed for the mechanical Route 3 skeleton. They simply record,
in Lean-typed form, two intermediate subtargets mentioned in
`renormalized_tail_bound.md` §8.8.
-/

namespace OptionalTargets

section DenseReduction

variable {F : Type} [TestSpace F] [TopologicalSpace F]
variable (L : LagariasFramework F)

/-- Target: reduce Weil positivity to a dense subclass, using continuity of the quadratic form. -/
def DenseSubclassReduction : Prop :=
  ∃ (S : Set F),
    Dense S ∧
    Continuous (fun f : F => (L.W1 (TestSpace.quad (F:=F) f)).re) ∧
      ((∀ f : F, f ∈ S → 0 ≤ (L.W1 (TestSpace.quad (F:=F) f)).re) →
        (∀ f : F, 0 ≤ (L.W1 (TestSpace.quad (F:=F) f)).re))

end DenseReduction

section LiEventualPositivity

variable {F : Type} [TestSpace F]
variable (L : LiFramework F)

/-- Target: a quantitative lower bound implying eventual Li positivity (hence a finite reduction). -/
def LiEventualPositivityTarget : Prop :=
  ∃ (N0 : ℕ) (c C θ : ℝ),
    θ < 1 ∧
    (∀ n : ℕ, N0 ≤ n →
      L.lambda n ≥ ((n : ℝ) / 2) * Real.log (n : ℝ) + c * (n : ℝ) - C * (n : ℝ) ^ θ)

end LiEventualPositivity

end OptionalTargets

end ExplicitFormula
end RiemannRecognitionGeometry

