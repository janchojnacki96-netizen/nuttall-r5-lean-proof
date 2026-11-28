import Nuttall.PsiCompactCell7Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell7Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 7) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 7) = psiOneCell7Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell7Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell7Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell7Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
