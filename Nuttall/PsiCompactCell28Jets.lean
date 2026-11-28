import Nuttall.PsiCompactCell28Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell28Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 28) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 28) = psiOneCell28Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell28Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell28Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell28Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
