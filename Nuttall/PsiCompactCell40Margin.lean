import Nuttall.PsiCompactCell40Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell40Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 40 psiOneCell40Snapshot.corner psiOneCell40Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell40Margin_checked

end Nuttall
