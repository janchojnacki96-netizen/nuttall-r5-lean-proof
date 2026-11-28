import Nuttall.PsiCompactCell7Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell7Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 7 psiOneCell7Snapshot.corner psiOneCell7Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell7Margin_checked

end Nuttall
