import Nuttall.PsiCompactCell13Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell13Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 13 psiOneCell13Snapshot.corner psiOneCell13Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell13Margin_checked

end Nuttall
