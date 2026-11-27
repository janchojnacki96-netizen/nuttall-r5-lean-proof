import Nuttall.PsiCompactCell60Data
import Nuttall.PsiCompactFixedJetCell

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell60Margin_checked (i : Fin 7) :
    psiOneCompactFixedRow 60 (psiOneCompactBoxesOfJets (1/256) psiOneCell60Corner
      psiOneCell60PhiJet) i < psiOneCompactFixedThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiOneCell60Margin_checked

end Nuttall
