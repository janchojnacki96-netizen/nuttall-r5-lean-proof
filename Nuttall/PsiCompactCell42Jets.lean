import Nuttall.PsiCompactCell42Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell42Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 42) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 42) = psiOneCell42Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell42Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell42Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell42Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
