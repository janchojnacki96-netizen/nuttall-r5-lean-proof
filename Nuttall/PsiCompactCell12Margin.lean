import Nuttall.PsiCompactCell12Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell12Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 12 psiOneCell12Snapshot.corner psiOneCell12Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell12Margin_checked

end Nuttall
