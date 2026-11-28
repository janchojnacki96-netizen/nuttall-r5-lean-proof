import Nuttall.PsiCompactCell12Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell12Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 12) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 12) = psiOneCell12Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell12Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell12Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell12Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
