import Nuttall.PhiCompactReplay.Batch00
import Nuttall.PhiCompactReplay.Batch01
import Nuttall.PhiCompactReplay.Batch02
import Nuttall.PhiCompactReplay.Batch03
import Nuttall.PhiCompactReplay.Batch04
import Nuttall.PhiCompactReplay.Batch05
import Nuttall.PhiCompactReplay.Batch06
import Nuttall.PhiCompactReplay.Batch07
import Nuttall.PhiCompactReplay.Batch08
import Nuttall.PhiCompactReplay.Batch09
import Nuttall.PhiCompactReplay.Batch10

namespace Nuttall

/-- The compact grid passes all four signed determinant checks in every closed cell. -/
theorem phiCompactGridChecked_proved : phiCompactGridChecked := by
  have h : phiCompactCells =
      ((phiCompactCells.drop 0).take 5) ++
      ((phiCompactCells.drop 5).take 5) ++
      ((phiCompactCells.drop 10).take 5) ++
      ((phiCompactCells.drop 15).take 5) ++
      ((phiCompactCells.drop 20).take 5) ++
      ((phiCompactCells.drop 25).take 5) ++
      ((phiCompactCells.drop 30).take 5) ++
      ((phiCompactCells.drop 35).take 5) ++
      ((phiCompactCells.drop 40).take 5) ++
      ((phiCompactCells.drop 45).take 5) ++
      ((phiCompactCells.drop 50).take 1) := by decide +kernel
  unfold phiCompactGridChecked
  rw [h]
  simp only [List.all_append, phiCompactReplay00, phiCompactReplay01, phiCompactReplay02,
    phiCompactReplay03, phiCompactReplay04, phiCompactReplay05, phiCompactReplay06,
    phiCompactReplay07, phiCompactReplay08, phiCompactReplay09, phiCompactReplay10, Bool.true_and]

#print axioms phiCompactGridChecked_proved

end Nuttall
