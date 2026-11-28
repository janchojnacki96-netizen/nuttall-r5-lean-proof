import Nuttall.PsiCompactCell17Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell17Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 17) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 17) = psiOneCell17Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell17Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell17Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell17Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
