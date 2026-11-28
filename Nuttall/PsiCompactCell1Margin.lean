import Nuttall.PsiCompactCell1Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell1Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 1 psiOneCell1Snapshot.corner psiOneCell1Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell1Margin_checked

end Nuttall
