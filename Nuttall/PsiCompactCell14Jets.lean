import Nuttall.PsiCompactCell14Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell14Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 14) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 14) = psiOneCell14Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell14Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell14Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell14Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
