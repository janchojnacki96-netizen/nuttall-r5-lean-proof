import Nuttall.PsiCompactCell3Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell3Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 3) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 3) = psiOneCell3Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell3Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell3Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell3Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
