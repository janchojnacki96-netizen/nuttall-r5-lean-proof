import Nuttall.PsiTwoCompactCell52Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell52Margin_checked (i : Fin 8) :
    psiTwoCompactRow psiTwoCell52Basis psiTwoCell52One psiTwoCell52Two
      psiTwoCell52Phi i < psiTwoCompactThreshold := by
  fin_cases i <;> decide +kernel

#print axioms psiTwoCell52Margin_checked

end Nuttall
