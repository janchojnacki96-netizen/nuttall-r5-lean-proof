import Nuttall.PsiCompactCell43Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell43Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 43 psiOneCell43Snapshot.corner psiOneCell43Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell43Margin_checked

end Nuttall
