import Nuttall.PsiCompactCell46Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell46Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 46) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 46) = psiOneCell46Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell46Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell46Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell46Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
