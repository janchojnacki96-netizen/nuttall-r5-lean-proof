import Nuttall.PsiCompactCell40Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell40Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 40) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 40) = psiOneCell40Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell40Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell40Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell40Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
