import Nuttall.PsiCompactCell34Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell34Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 34) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 34) = psiOneCell34Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell34Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell34Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell34Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
