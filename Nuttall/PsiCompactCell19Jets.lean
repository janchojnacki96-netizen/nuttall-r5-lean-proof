import Nuttall.PsiCompactCell19Data

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell19Inputs_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 19) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 19) = psiOneCell19Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneCell19Jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell19Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell19Snapshot.input j := by
  interval_cases j <;> decide +kernel

end Nuttall
