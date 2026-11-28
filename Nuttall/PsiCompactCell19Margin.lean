import Nuttall.PsiCompactCell19Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell19Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 19 psiOneCell19Snapshot.corner psiOneCell19Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell19Margin_checked

end Nuttall
