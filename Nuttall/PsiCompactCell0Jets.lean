import Nuttall.PsiCompactCell0Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell0Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 0) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 0) = psiOneCell0Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell0Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell0Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell0Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
