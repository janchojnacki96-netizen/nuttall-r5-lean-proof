import Nuttall.PsiCompactCell33Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell33Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 33 psiOneCell33Snapshot.corner psiOneCell33Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell33Margin_checked

end Nuttall
