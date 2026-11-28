import Nuttall.PsiCompactCell30Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell30Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 30) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 30) = psiOneCell30Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell30Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell30Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell30Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
