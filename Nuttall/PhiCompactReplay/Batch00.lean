import Nuttall.PhiCompactCells

namespace Nuttall

private theorem cell0 : phiCompactCellPass phiCompactCells[0]! = true := by
  have h : phiCompactCells[0]! = (3, 3085/1024) := by decide +kernel
  simpa only [h] using phiCompact_first_cell_pass

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell1 : phiCompactCellPass phiCompactCells[1]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell2 : phiCompactCellPass phiCompactCells[2]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell3 : phiCompactCellPass phiCompactCells[3]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell4 : phiCompactCellPass phiCompactCells[4]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 0 through 4. -/
theorem phiCompactReplay00 :
    ((phiCompactCells.drop 0).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 0).take 5 =
      [phiCompactCells[0]!, phiCompactCells[1]!, phiCompactCells[2]!, phiCompactCells[3]!, phiCompactCells[4]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell0, cell1, cell2, cell3, cell4, Bool.true_and]

end Nuttall
