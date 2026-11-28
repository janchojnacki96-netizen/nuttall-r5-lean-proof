import Nuttall.PsiCompactCell25Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell25Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 25) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 25) = psiOneCell25Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell25Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell25Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell25Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
