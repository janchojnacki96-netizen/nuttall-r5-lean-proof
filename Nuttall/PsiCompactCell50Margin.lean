import Nuttall.PsiCompactCell50Data
import Nuttall.PsiOneCompactDyadicCell

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell50Margin_checked (i : Fin 7) :
    psiOneCompactDyadicRow 50 psiOneCell50CornerFixed psiOneCell50PhiJetFixed i <
      psiOneCompactDyadicThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiOneCell50Margin_checked

end Nuttall
