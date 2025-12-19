/-
# Port glue: bundle S2 (trace + pairing) assumptions into the bundled CR/Green targets

This file is purely “wiring”:

- xi-side faithful interface: `Port.XiCRGreenS2.Assumptions`
- cofactor-side faithful interface: `Port.CofactorCRGreenS2.Assumptions`

These imply the strong (faithful) energy-form targets
`XiCRGreenAssumptionsStrong` / `CofactorCRGreenAssumptionsStrong`,
and hence the bundled `EnergyCRGreenAssumptionsStrong` (and then the weaker bundle).

No analysis is proved here.
-/

import RiemannRecognitionGeometry.Port.EnergyCRGreenAssumptions
import RiemannRecognitionGeometry.Port.XiCRGreenS2
import RiemannRecognitionGeometry.Port.CofactorCRGreenS2

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

/-- Bundle xi+cofactor S2 assumptions into the bundled **strong** energy-form CR/Green targets. -/
theorem energyCRGreenAssumptionsStrong_of_S2
    (hXi : XiCRGreenS2.Assumptions)
    (hCof : CofactorCRGreenS2.Assumptions) :
    EnergyCRGreenAssumptionsStrong := by
  refine ⟨?_, ?_⟩
  · exact XiCRGreenS2.xiCRGreenAssumptionsStrong_of_S2 hXi
  · exact CofactorCRGreenS2.cofactorCRGreenAssumptionsStrong_of_S2 hCof

/-- Bundle xi+cofactor S2 assumptions into the bundled (weak) energy-based CR/Green targets. -/
theorem energyCRGreenAssumptions_of_S2
    (hXi : XiCRGreenS2.Assumptions)
    (hCof : CofactorCRGreenS2.Assumptions) :
    EnergyCRGreenAssumptions :=
  energyCRGreenAssumptions_of_strong (energyCRGreenAssumptionsStrong_of_S2 hXi hCof)

end Port
end RiemannRecognitionGeometry
