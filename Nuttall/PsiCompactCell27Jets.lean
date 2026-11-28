import Nuttall.PsiCompactCell27Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell27Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 27) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 27) = psiOneCell27Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell27Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell27Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell27Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
