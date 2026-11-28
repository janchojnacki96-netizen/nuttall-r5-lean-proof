import Nuttall.PsiCompactCell34Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell34Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 34 psiOneCell34Snapshot.corner psiOneCell34Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell34Margin_checked

end Nuttall
