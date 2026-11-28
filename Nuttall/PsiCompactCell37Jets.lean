import Nuttall.PsiCompactCell37Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell37Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 37) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 37) = psiOneCell37Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell37Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell37Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell37Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
