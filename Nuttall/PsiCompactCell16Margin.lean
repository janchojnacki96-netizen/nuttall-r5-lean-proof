import Nuttall.PsiCompactCell16Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell16Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 16 psiOneCell16Snapshot.corner psiOneCell16Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell16Margin_checked

end Nuttall
