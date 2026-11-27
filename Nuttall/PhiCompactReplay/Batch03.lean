import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell15 : phiCompactCellPass phiCompactCells[15]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell16 : phiCompactCellPass phiCompactCells[16]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell17 : phiCompactCellPass phiCompactCells[17]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell18 : phiCompactCellPass phiCompactCells[18]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell19 : phiCompactCellPass phiCompactCells[19]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 15 through 19. -/
theorem phiCompactReplay03 :
    ((phiCompactCells.drop 15).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 15).take 5 =
      [phiCompactCells[15]!, phiCompactCells[16]!, phiCompactCells[17]!, phiCompactCells[18]!, phiCompactCells[19]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell15, cell16, cell17, cell18, cell19, Bool.true_and]

end Nuttall
