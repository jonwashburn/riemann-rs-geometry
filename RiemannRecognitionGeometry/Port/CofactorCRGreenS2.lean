import RiemannRecognitionGeometry.Port.CofactorCRGreenS2Interfaces
import RiemannRecognitionGeometry.Port.CofactorOuterLogBranch

noncomputable section

namespace RiemannRecognitionGeometry
namespace Port

open Real Complex

namespace CofactorCRGreenS2

/-- `S2` (faithful form): there exists a lift-based Green trace identity plus its pairing bound.

This avoids differentiating the principal-branch `arg` and instead works with a genuine real-valued
lift `θ` whose coercion agrees with the cofactor `Real.Angle` phase on the Whitney base. -/
def Assumptions : Prop :=
  ∃ h : CofactorOuterLogBranch.CofactorOuterLogBranch,
    CofactorCRGreenS2Interfaces.PairingBound (CofactorOuterLogBranch.greenTraceIdentity h)

/-- `S2a` + `S2b` ⇒ the strong cofactor CR/Green bound. -/
theorem cofactorCRGreenAssumptionsStrong_of_S2 (h : Assumptions) :
    CofactorCRGreenAssumptionsStrong := by
  rcases h with ⟨hOLB, hB⟩
  exact
    CofactorCRGreenS2Interfaces.cofactorCRGreenAssumptionsStrong_of_greenTrace_and_pairing
      (CofactorOuterLogBranch.greenTraceIdentity hOLB) hB

/-- `S2` (trace + pairing) also discharges the weaker energy-based cofactor CR/Green API by
composing `S2 → Strong → Weak`. -/
theorem cofactorCRGreenAssumptions_of_S2 (h : Assumptions) :
    CofactorCRGreenAssumptions :=
  cofactorCRGreenAssumptions_of_cofactorCRGreenAssumptionsStrong
    (cofactorCRGreenAssumptionsStrong_of_S2 h)

/-- `S2` also discharges the generic Hardy/Dirichlet CR/Green interface for
`Ebox := cofactorEbox_poisson`. -/
theorem hardyDirichletCRGreen_of_S2 (h : Assumptions) :
    HardyDirichletCRGreen cofactorEbox_poisson :=
  hardyDirichletCRGreen_of_cofactorCRGreenAssumptions (cofactorCRGreenAssumptions_of_S2 h)

/-- `S2` also discharges the **strong** Hardy/Dirichlet CR/Green interface for
`Ebox := cofactorEbox_poisson`. -/
theorem hardyDirichletCRGreenStrong_of_S2 (h : Assumptions) :
    HardyDirichletCRGreenStrong cofactorEbox_poisson :=
  hardyDirichletCRGreenStrong_of_cofactorCRGreenAssumptionsStrong
    (cofactorCRGreenAssumptionsStrong_of_S2 h)

end CofactorCRGreenS2

end Port
end RiemannRecognitionGeometry
