import Nuttall.PsiCompactCell38Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell38Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 38) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 38) = psiOneCell38Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell38Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell38Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell38Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
