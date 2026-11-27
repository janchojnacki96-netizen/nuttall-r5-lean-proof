import Nuttall.PsiFirstCellJets
import Nuttall.PsiFirstCellJetData
import Nuttall.CompactIntervalRounding

namespace Nuttall

open W5

private def firstCellJetEndpointCheck (j : ℕ) : Prop :=
  (psiOneFirstCellDyadicJetBox j).lo ≤ (psiOneFirstCellJetBox j).lo ∧
  (psiOneFirstCellJetBox j).hi ≤ (psiOneFirstCellDyadicJetBox j).hi

private instance (j : ℕ) : Decidable (firstCellJetEndpointCheck j) := by
  unfold firstCellJetEndpointCheck
  infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 40000000 in
private theorem firstCellJetEndpointCheck_of_lt (j : ℕ) (hj : j < 36) :
    firstCellJetEndpointCheck j := by
  interval_cases j <;> decide +kernel

theorem psiOneFirstCellDyadicJetBox_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneFirstCellDyadicJetBox j).ContainsReal (iteratedDeriv (j+1) (psi 1) (1/256)) :=
  compactContainsReal_of_endpoints (firstCellJetEndpointCheck_of_lt j hj).1
    (firstCellJetEndpointCheck_of_lt j hj).2 (psiOneFirstCellJetBox_containsReal j)

#print axioms psiOneFirstCellDyadicJetBox_containsReal

end Nuttall
