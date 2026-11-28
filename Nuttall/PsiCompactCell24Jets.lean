import Nuttall.PsiCompactCell24Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell24Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 24) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 24) = psiOneCell24Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell24Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell24Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell24Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
