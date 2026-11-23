import W5.ThetaAuditedMatrixRefinementReuse
import W5.ThetaBulkDegreeSelectedGammaCells
import W5.ThetaGammaPilotLastCell

/-!
# Cheap last-cell ORIGINAL audit inclusion pilot

Before attempting 51 expensive 5x5 LDL evaluations, test the two
matrix entries that dominate the last fifth-pivot uncertainty:
(4,4) first, (3,4) second. The target intervals are the ORIGINAL
768-bit audit boxes whose pivot signs already passed native_decide.

This uses only the CI-certified real-sound selected Gamma generator,
not any unverified numerical hypothesis. The #eval values are
diagnostics; false merely means the new generated interval is not
yet a refinement of the imported audit box.
-/

namespace W5

def thetaLastAuditPilotSource : ThetaIntervalMatrix :=
  thetaBulkDegreeSelectedCellMatrix
    8 thetaGammaPilotGrid ({7, 8} : Finset ℕ) ∅
    thetaGammaPilotLastLeft thetaGammaPilotLastRight

/-- Return lower and upper inclusion checks separately, identifying
which side of the original audited interval needs better precision. -/
def thetaLastAuditPilotBounds (i j : Fin 5) : List Bool :=
  let A := thetaAuditUpperCell_51 i j
  let B := thetaLastAuditPilotSource i j
  [decide (A.lo ≤ B.lo), decide (B.hi ≤ A.hi)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
#eval [thetaLastAuditPilotBounds 4 4, thetaLastAuditPilotBounds 3 4]

end W5
