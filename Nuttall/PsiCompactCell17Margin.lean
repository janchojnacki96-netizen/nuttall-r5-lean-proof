import Nuttall.PsiCompactCell17Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell17Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 17 psiOneCell17Snapshot.corner psiOneCell17Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell17Margin_checked

end Nuttall
