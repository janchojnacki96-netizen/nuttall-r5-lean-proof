import Nuttall.PsiLastCellGridInputs
import Nuttall.PsiFixedGridJets

namespace Nuttall

open W5

def lastCellPanelWidth (i : Fin 7) : ℚ :=
  if i = 0 then 1/512 else 1/32

def lastCellPanelRaw (i : Fin 7) : QInterval :=
  psiOnePanelBox (QInterval.point 0) (psiFixedGridPhiJetBoxOfInputs (psiLastCellGridInputs i))
    36 (lastCellPanelWidth i)

private def lastCellPanelCheck (i : Fin 7) : Prop :=
  (psiLastCellPanelSnapshot i).lo ≤ (lastCellPanelRaw i).lo ∧
    (lastCellPanelRaw i).hi ≤ (psiLastCellPanelSnapshot i).hi

private instance (i : Fin 7) : Decidable (lastCellPanelCheck i) := by
  unfold lastCellPanelCheck
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem lastCellPanel_checked (i : Fin 7) : lastCellPanelCheck i := by
  fin_cases i <;> decide +kernel

#print axioms lastCellPanel_checked

end Nuttall
