import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell35 : phiCompactCellPass phiCompactCells[35]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell36 : phiCompactCellPass phiCompactCells[36]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell37 : phiCompactCellPass phiCompactCells[37]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell38 : phiCompactCellPass phiCompactCells[38]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell39 : phiCompactCellPass phiCompactCells[39]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 35 through 39. -/
theorem phiCompactReplay07 :
    ((phiCompactCells.drop 35).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 35).take 5 =
      [phiCompactCells[35]!, phiCompactCells[36]!, phiCompactCells[37]!, phiCompactCells[38]!, phiCompactCells[39]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell35, cell36, cell37, cell38, cell39, Bool.true_and]

end Nuttall
