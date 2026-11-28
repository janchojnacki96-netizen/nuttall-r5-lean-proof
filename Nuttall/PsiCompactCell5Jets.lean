import Nuttall.PsiCompactCell5Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell5Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 5) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 5) = psiOneCell5Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell5Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell5Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell5Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
