import Nuttall.PsiCompactCell15Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell15Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 15 psiOneCell15Snapshot.corner psiOneCell15Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell15Margin_checked

end Nuttall
