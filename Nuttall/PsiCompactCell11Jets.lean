import Nuttall.PsiCompactCell11Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell11Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 11) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 11) = psiOneCell11Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell11Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell11Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell11Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
