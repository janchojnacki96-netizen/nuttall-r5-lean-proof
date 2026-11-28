import Nuttall.PsiCompactCell25Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell25Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 25 psiOneCell25Snapshot.corner psiOneCell25Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell25Margin_checked

end Nuttall
