import Nuttall.PsiTwoCompactCell50Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell50Margin_checked (i : Fin 8) :
    psiTwoCompactRow psiTwoCell50Basis psiOneCell50CornerFixed psiTwoCell50Two
      psiOneCell50PhiJetFixed i < psiTwoCompactThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiTwoCell50Margin_checked

end Nuttall
