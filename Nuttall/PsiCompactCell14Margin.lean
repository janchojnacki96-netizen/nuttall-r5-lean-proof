import Nuttall.PsiCompactCell14Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell14Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 14 psiOneCell14Snapshot.corner psiOneCell14Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell14Margin_checked

end Nuttall
