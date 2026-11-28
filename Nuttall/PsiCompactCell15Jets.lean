import Nuttall.PsiCompactCell15Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell15Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 15) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 15) = psiOneCell15Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell15Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell15Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell15Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
