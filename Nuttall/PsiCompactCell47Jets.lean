import Nuttall.PsiCompactCell47Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell47Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 47) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 47) = psiOneCell47Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell47Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell47Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell47Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
