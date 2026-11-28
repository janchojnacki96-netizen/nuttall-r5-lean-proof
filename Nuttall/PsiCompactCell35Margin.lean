import Nuttall.PsiCompactCell35Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell35Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 35 psiOneCell35Snapshot.corner psiOneCell35Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell35Margin_checked

end Nuttall
