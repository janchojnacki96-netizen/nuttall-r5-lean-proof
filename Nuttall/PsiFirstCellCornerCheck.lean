import Nuttall.PsiFirstCellCorner
import Nuttall.PsiFirstCellJetData
import Nuttall.CompactIntervalRounding

namespace Nuttall

open W5

set_option maxRecDepth 32768 in
set_option maxHeartbeats 40000000 in
private theorem psiOneFirstCellCorner_endpoints :
    psiOneFirstCellFixedCorner.lo ≤ psiOneFirstCellCornerBox.lo ∧
    psiOneFirstCellCornerBox.hi ≤ psiOneFirstCellFixedCorner.hi := by
  decide_cbv

theorem psiOneFirstCellFixedCorner_containsReal :
    psiOneFirstCellFixedCorner.ContainsReal (psi 1 (1/256)) :=
  compactContainsReal_of_endpoints psiOneFirstCellCorner_endpoints.1
    psiOneFirstCellCorner_endpoints.2 psiOne_first_cell_corner_containsReal

#print axioms psiOneFirstCellFixedCorner_containsReal

end Nuttall
