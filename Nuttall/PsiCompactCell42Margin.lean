import Nuttall.PsiCompactCell42Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell42Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 42 psiOneCell42Snapshot.corner psiOneCell42Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell42Margin_checked

end Nuttall
