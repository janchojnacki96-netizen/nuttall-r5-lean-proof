import Nuttall.PsiCompactCell24Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell24Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 24 psiOneCell24Snapshot.corner psiOneCell24Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell24Margin_checked

end Nuttall
