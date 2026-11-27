import Nuttall.PsiCompactCell47Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell47Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 47 psiOneCell47Snapshot.corner psiOneCell47Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell47Margin_checked

end Nuttall
