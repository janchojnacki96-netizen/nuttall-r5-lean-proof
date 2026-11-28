import Nuttall.PsiCompactCell32Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell32Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 32) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 32) = psiOneCell32Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell32Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell32Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell32Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
