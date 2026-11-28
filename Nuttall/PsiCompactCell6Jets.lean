import Nuttall.PsiCompactCell6Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell6Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 6) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 6) = psiOneCell6Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell6Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell6Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell6Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
