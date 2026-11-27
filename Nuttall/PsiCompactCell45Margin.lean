import Nuttall.PsiCompactCell45Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell45Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 45 psiOneCell45Snapshot.corner psiOneCell45Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell45Margin_checked

end Nuttall
