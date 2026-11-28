import Nuttall.PsiCompactCell23Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell23Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 23) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 23) = psiOneCell23Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell23Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell23Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell23Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
