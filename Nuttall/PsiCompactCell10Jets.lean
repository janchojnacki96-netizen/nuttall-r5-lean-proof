import Nuttall.PsiCompactCell10Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell10Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 10) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 10) = psiOneCell10Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell10Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell10Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell10Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
