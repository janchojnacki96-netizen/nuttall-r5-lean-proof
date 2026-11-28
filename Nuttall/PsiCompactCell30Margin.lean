import Nuttall.PsiCompactCell30Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell30Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 30 psiOneCell30Snapshot.corner psiOneCell30Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell30Margin_checked

end Nuttall
