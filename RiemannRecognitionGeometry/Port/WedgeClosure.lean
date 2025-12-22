/-
# Port alignment: wedge closure / boundary positivity interfaces

The `reality` blueprint has a disabled “wedge closure” module:
`IndisputableMonolith/RH/HardyDirichlet/WedgeClosure.lean.disabled`,
whose role is to combine:

- a Poisson plateau lower bound, and
- a CR/Green + Carleson upper bound,

into an a.e. **boundary positivity** statement that then feeds the Schur pinch argument.

In this repo, the analogous “boundary wedge” interface is already mined and factored in Route 3 as:

- `RiemannRecognitionGeometry/ExplicitFormula/BoundaryWedgeInterfaces.lean`, and
- lightweight wrappers in `PPlusZetaShim.lean` that consume the mined wedge assumptions.

This file re-exports the key interface path via `Port/*` so the Reality port plan can refer to
a stable location while we continue replacing interface fields with proofs.
-/

import RiemannRecognitionGeometry.ExplicitFormula.PPlusZetaShim

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

namespace WedgeClosure

open MeasureTheory
open scoped Real

open RiemannRecognitionGeometry.ExplicitFormula

/-- Re-export of the mined boundary-wedge assumptions interface (ζ instantiation). -/
abbrev BoundaryWedgeAssumptions (H : ExplicitFormula.ZetaInstantiation.ZetaPSCHypotheses) :=
  ExplicitFormula.ZetaInstantiation.BoundaryWedgeAssumptions H

/-- Re-export: boundary phase positivity for ζ from the wedge interface (the “wedge closure output”). -/
theorem boundaryPhase_cos_nonneg_ae (H : ExplicitFormula.ZetaInstantiation.ZetaPSCHypotheses)
    (wedge : BoundaryWedgeAssumptions H) :
    (∀ᵐ t : ℝ, 0 ≤ Real.cos (H.boundaryPhase t)) :=
  ExplicitFormula.ZetaInstantiation.boundaryPhase_cos_nonneg_ae H wedge

end WedgeClosure

end Port
end RiemannRecognitionGeometry
