import Nuttall.PsiCompactCell1Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell1Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 1) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 1) = psiOneCell1Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell1Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell1Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell1Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
