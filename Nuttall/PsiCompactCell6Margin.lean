import Nuttall.PsiCompactCell6Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell6Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 6 psiOneCell6Snapshot.corner psiOneCell6Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell6Margin_checked

end Nuttall
