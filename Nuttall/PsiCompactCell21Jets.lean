import Nuttall.PsiCompactCell21Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell21Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 21) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 21) = psiOneCell21Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell21Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell21Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell21Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
