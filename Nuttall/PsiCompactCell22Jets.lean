import Nuttall.PsiCompactCell22Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell22Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 22) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 22) = psiOneCell22Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell22Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell22Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell22Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
