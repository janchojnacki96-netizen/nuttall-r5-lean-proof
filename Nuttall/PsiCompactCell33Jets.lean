import Nuttall.PsiCompactCell33Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell33Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 33) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 33) = psiOneCell33Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell33Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell33Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell33Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
