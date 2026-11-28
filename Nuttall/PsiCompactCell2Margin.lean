import Nuttall.PsiCompactCell2Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell2Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 2 psiOneCell2Snapshot.corner psiOneCell2Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell2Margin_checked

end Nuttall
