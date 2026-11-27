import Nuttall.PsiCompactFixedCellSigns
import Nuttall.PsiCompactCellCoefficients
import Nuttall.PsiLastCellJetData

namespace Nuttall

open W5

def psiOneLastCellCoeffBox (l k : ℕ) : QInterval :=
  let J := match l+k with
    | 0 => psiOneLastCellCornerSnapshot
    | j+1 => psiOneLastCellJetSnapshot j
  psiOneCompactCoefficientBoxOfJet (1/512) J l k

def psiOneLastCellBoxes (k : ℕ) : Matrix (Fin 7) (Fin 7) QInterval :=
  Matrix.of fun i j => psiOneLastCellCoeffBox (i.val+j.val) k

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneLastCellMargin_checked (i : Fin 7) :
    psiOneCompactFixedRow 66 psiOneLastCellBoxes i < psiOneCompactFixedThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiOneLastCellMargin_checked

end Nuttall
