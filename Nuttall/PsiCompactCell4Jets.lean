import Nuttall.PsiCompactCell4Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell4Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 4) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 4) = psiOneCell4Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell4Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell4Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell4Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
