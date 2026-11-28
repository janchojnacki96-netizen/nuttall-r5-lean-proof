import Nuttall.PsiCompactCell35Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell35Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 35) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 35) = psiOneCell35Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell35Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell35Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell35Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
