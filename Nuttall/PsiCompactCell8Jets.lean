import Nuttall.PsiCompactCell8Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell8Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 8) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 8) = psiOneCell8Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell8Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell8Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell8Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
