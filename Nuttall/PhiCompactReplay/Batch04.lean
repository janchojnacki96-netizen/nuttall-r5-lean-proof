import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell20 : phiCompactCellPass phiCompactCells[20]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell21 : phiCompactCellPass phiCompactCells[21]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell22 : phiCompactCellPass phiCompactCells[22]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell23 : phiCompactCellPass phiCompactCells[23]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell24 : phiCompactCellPass phiCompactCells[24]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 20 through 24. -/
theorem phiCompactReplay04 :
    ((phiCompactCells.drop 20).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 20).take 5 =
      [phiCompactCells[20]!, phiCompactCells[21]!, phiCompactCells[22]!, phiCompactCells[23]!, phiCompactCells[24]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell20, cell21, cell22, cell23, cell24, Bool.true_and]

end Nuttall
