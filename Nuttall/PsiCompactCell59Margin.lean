import Nuttall.PsiCompactCell59Data
import Nuttall.PsiCompactFixedJetCell

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell59Margin_checked (i : Fin 7) :
    psiOneCompactFixedRow 59 (psiOneCompactBoxesOfJets (1/256) psiOneCell59Corner
      psiOneCell59PhiJet) i < psiOneCompactFixedThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiOneCell59Margin_checked

end Nuttall
