import Nuttall.PsiCompactCell46Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell46Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 46 psiOneCell46Snapshot.corner psiOneCell46Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell46Margin_checked

end Nuttall
