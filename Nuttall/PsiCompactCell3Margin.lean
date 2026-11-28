import Nuttall.PsiCompactCell3Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell3Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 3 psiOneCell3Snapshot.corner psiOneCell3Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell3Margin_checked

end Nuttall
