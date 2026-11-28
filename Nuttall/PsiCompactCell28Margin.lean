import Nuttall.PsiCompactCell28Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell28Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 28 psiOneCell28Snapshot.corner psiOneCell28Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell28Margin_checked

end Nuttall
