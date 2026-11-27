import Nuttall.PsiCompactCell44Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell44Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 44 psiOneCell44Snapshot.corner psiOneCell44Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell44Margin_checked

end Nuttall
