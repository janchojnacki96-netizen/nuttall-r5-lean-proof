import Nuttall.PsiCompactCell31Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell31Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 31) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 31) = psiOneCell31Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell31Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell31Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell31Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
