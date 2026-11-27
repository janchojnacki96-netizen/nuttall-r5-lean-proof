import Nuttall.PsiCompactCell45Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell45Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 45) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 45) = psiOneCell45Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell45Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell45Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell45Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
