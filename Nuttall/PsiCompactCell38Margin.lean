import Nuttall.PsiCompactCell38Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell38Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 38 psiOneCell38Snapshot.corner psiOneCell38Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell38Margin_checked

end Nuttall
