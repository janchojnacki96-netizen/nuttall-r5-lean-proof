import Nuttall.PsiCompactCell39Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell39Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 39) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 39) = psiOneCell39Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell39Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell39Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell39Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
