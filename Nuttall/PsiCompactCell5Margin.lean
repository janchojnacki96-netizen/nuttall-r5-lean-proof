import Nuttall.PsiCompactCell5Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell5Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 5 psiOneCell5Snapshot.corner psiOneCell5Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell5Margin_checked

end Nuttall
