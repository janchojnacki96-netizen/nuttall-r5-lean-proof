import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell5 : phiCompactCellPass phiCompactCells[5]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell6 : phiCompactCellPass phiCompactCells[6]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell7 : phiCompactCellPass phiCompactCells[7]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell8 : phiCompactCellPass phiCompactCells[8]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell9 : phiCompactCellPass phiCompactCells[9]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 5 through 9. -/
theorem phiCompactReplay01 :
    ((phiCompactCells.drop 5).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 5).take 5 =
      [phiCompactCells[5]!, phiCompactCells[6]!, phiCompactCells[7]!, phiCompactCells[8]!, phiCompactCells[9]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell5, cell6, cell7, cell8, cell9, Bool.true_and]

end Nuttall
