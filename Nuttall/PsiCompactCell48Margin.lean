import Nuttall.PsiCompactCell48Data
import Nuttall.PsiOneCompactDyadicCell

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell48Margin_checked (i : Fin 7) :
    psiOneCompactDyadicRow 48 psiOneCell48CornerFixed psiOneCell48PhiJetFixed i <
      psiOneCompactDyadicThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiOneCell48Margin_checked

end Nuttall
