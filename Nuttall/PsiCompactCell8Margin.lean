import Nuttall.PsiCompactCell8Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell8Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 8 psiOneCell8Snapshot.corner psiOneCell8Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell8Margin_checked

end Nuttall
