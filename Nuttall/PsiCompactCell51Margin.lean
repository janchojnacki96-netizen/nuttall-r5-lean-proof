import Nuttall.PsiCompactCell51Data
import Nuttall.PsiOneCompactDyadicCell

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell51Margin_checked (i : Fin 7) :
    psiOneCompactDyadicRow 51 psiOneCell51CornerFixed psiOneCell51PhiJetFixed i <
      psiOneCompactDyadicThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiOneCell51Margin_checked

end Nuttall
