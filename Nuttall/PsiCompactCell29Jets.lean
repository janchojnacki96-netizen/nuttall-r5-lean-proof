import Nuttall.PsiCompactCell29Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell29Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 29) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 29) = psiOneCell29Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell29Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell29Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell29Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
