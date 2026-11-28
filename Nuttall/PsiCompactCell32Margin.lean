import Nuttall.PsiCompactCell32Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell32Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 32 psiOneCell32Snapshot.corner psiOneCell32Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell32Margin_checked

end Nuttall
