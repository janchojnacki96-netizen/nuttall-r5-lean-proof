import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell10 : phiCompactCellPass phiCompactCells[10]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell11 : phiCompactCellPass phiCompactCells[11]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell12 : phiCompactCellPass phiCompactCells[12]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell13 : phiCompactCellPass phiCompactCells[13]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell14 : phiCompactCellPass phiCompactCells[14]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 10 through 14. -/
theorem phiCompactReplay02 :
    ((phiCompactCells.drop 10).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 10).take 5 =
      [phiCompactCells[10]!, phiCompactCells[11]!, phiCompactCells[12]!, phiCompactCells[13]!, phiCompactCells[14]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell10, cell11, cell12, cell13, cell14, Bool.true_and]

end Nuttall
