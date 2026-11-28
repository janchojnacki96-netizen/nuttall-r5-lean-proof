import Nuttall.PsiCompactCell41Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell41Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 41) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 41) = psiOneCell41Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell41Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell41Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell41Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
