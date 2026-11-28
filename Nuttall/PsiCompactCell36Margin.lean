import Nuttall.PsiCompactCell36Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell36Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 36 psiOneCell36Snapshot.corner psiOneCell36Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell36Margin_checked

end Nuttall
