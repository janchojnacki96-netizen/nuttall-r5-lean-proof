import Nuttall.PsiTwoCompactCell48Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell48Margin_checked (i : Fin 8) :
    psiTwoCompactRow psiTwoCell48Basis psiOneCell48CornerFixed psiTwoCell48Two
      psiOneCell48PhiJetFixed i < psiTwoCompactThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiTwoCell48Margin_checked

end Nuttall
