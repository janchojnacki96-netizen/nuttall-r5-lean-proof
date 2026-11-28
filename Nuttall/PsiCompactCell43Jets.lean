import Nuttall.PsiCompactCell43Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell43Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 43) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 43) = psiOneCell43Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell43Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell43Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell43Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
