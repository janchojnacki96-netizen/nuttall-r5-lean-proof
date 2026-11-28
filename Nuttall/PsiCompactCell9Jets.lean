import Nuttall.PsiCompactCell9Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell9Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 9) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 9) = psiOneCell9Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell9Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell9Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell9Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
