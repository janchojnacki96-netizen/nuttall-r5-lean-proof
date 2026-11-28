import Nuttall.PsiCompactCell26Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell26Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 26 psiOneCell26Snapshot.corner psiOneCell26Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell26Margin_checked

end Nuttall
