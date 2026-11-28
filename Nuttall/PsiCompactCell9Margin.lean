import Nuttall.PsiCompactCell9Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell9Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 9 psiOneCell9Snapshot.corner psiOneCell9Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell9Margin_checked

end Nuttall
