import Nuttall.PsiCompactCell18Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell18Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 18) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 18) = psiOneCell18Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell18Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell18Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell18Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
