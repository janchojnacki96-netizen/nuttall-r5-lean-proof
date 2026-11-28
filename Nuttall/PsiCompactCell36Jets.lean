import Nuttall.PsiCompactCell36Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell36Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 36) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 36) = psiOneCell36Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell36Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell36Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell36Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
