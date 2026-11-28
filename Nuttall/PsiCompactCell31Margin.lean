import Nuttall.PsiCompactCell31Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell31Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 31 psiOneCell31Snapshot.corner psiOneCell31Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell31Margin_checked

end Nuttall
