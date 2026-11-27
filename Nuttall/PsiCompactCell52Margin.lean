import Nuttall.PsiCompactCell52Data
import Nuttall.PsiCompactFixedJetCell

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell52Margin_checked (i : Fin 7) :
    psiOneCompactFixedRow 52 (psiOneCompactBoxesOfJets (1/256) psiOneCell52Corner
      psiOneCell52PhiJet) i < psiOneCompactFixedThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiOneCell52Margin_checked

end Nuttall
