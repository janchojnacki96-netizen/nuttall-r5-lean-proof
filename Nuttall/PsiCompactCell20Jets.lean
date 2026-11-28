import Nuttall.PsiCompactCell20Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell20Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 20) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 20) = psiOneCell20Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell20Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell20Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell20Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
