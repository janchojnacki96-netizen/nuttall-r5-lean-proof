import Nuttall.PsiTwoCompactCell51Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell51Margin_checked (i : Fin 8) :
    psiTwoCompactRow psiTwoCell51Basis psiOneCell51CornerFixed psiTwoCell51Two
      psiOneCell51PhiJetFixed i < psiTwoCompactThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiTwoCell51Margin_checked

end Nuttall
