import Nuttall.PsiCompactCell22Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell22Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 22 psiOneCell22Snapshot.corner psiOneCell22Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell22Margin_checked

end Nuttall
