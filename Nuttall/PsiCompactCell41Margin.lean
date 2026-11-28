import Nuttall.PsiCompactCell41Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell41Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 41 psiOneCell41Snapshot.corner psiOneCell41Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell41Margin_checked

end Nuttall
