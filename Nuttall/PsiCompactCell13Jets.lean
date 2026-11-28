import Nuttall.PsiCompactCell13Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell13Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 13) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 13) = psiOneCell13Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell13Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell13Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell13Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
