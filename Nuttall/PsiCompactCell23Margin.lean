import Nuttall.PsiCompactCell23Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell23Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 23 psiOneCell23Snapshot.corner psiOneCell23Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell23Margin_checked

end Nuttall
