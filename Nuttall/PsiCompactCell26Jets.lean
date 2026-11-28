import Nuttall.PsiCompactCell26Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell26Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 26) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 26) = psiOneCell26Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell26Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell26Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell26Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
