import Nuttall.PsiCompactCell2Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell2Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 2) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 2) = psiOneCell2Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell2Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell2Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell2Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
