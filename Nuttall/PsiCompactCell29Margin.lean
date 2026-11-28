import Nuttall.PsiCompactCell29Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell29Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 29 psiOneCell29Snapshot.corner psiOneCell29Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell29Margin_checked

end Nuttall
