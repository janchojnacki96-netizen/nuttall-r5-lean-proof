import Nuttall.PsiCompactCell20Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell20Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 20 psiOneCell20Snapshot.corner psiOneCell20Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell20Margin_checked

end Nuttall
