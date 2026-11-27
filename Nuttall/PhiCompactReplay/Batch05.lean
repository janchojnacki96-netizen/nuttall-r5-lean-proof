import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell25 : phiCompactCellPass phiCompactCells[25]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell26 : phiCompactCellPass phiCompactCells[26]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell27 : phiCompactCellPass phiCompactCells[27]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell28 : phiCompactCellPass phiCompactCells[28]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell29 : phiCompactCellPass phiCompactCells[29]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 25 through 29. -/
theorem phiCompactReplay05 :
    ((phiCompactCells.drop 25).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 25).take 5 =
      [phiCompactCells[25]!, phiCompactCells[26]!, phiCompactCells[27]!, phiCompactCells[28]!, phiCompactCells[29]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell25, cell26, cell27, cell28, cell29, Bool.true_and]

end Nuttall
