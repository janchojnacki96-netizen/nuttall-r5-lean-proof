import Nuttall.PsiCompactCell49Data
import Nuttall.PsiOneCompactDyadicCell

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell49Margin_checked (i : Fin 7) :
    psiOneCompactDyadicRow 49 psiOneCell49CornerFixed psiOneCell49PhiJetFixed i <
      psiOneCompactDyadicThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiOneCell49Margin_checked

end Nuttall
