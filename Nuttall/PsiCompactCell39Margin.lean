import Nuttall.PsiCompactCell39Data

namespace Nuttall

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell39Margin_checked (j : Fin 7) :
    psiOneCompactDyadicRow 39 psiOneCell39Snapshot.corner psiOneCell39Snapshot.jets j <
      psiOneCompactDyadicThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiOneCell39Margin_checked

end Nuttall
