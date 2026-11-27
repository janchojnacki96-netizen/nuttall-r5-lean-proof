import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell40 : phiCompactCellPass phiCompactCells[40]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell41 : phiCompactCellPass phiCompactCells[41]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell42 : phiCompactCellPass phiCompactCells[42]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell43 : phiCompactCellPass phiCompactCells[43]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell44 : phiCompactCellPass phiCompactCells[44]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 40 through 44. -/
theorem phiCompactReplay08 :
    ((phiCompactCells.drop 40).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 40).take 5 =
      [phiCompactCells[40]!, phiCompactCells[41]!, phiCompactCells[42]!, phiCompactCells[43]!, phiCompactCells[44]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell40, cell41, cell42, cell43, cell44, Bool.true_and]

end Nuttall
