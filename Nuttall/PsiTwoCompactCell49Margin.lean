import Nuttall.PsiTwoCompactCell49Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell49Margin_checked (i : Fin 8) :
    psiTwoCompactRow psiTwoCell49Basis psiOneCell49CornerFixed psiTwoCell49Two
      psiOneCell49PhiJetFixed i < psiTwoCompactThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiTwoCell49Margin_checked

end Nuttall
