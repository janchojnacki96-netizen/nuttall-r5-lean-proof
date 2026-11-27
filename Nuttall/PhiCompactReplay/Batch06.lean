import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell30 : phiCompactCellPass phiCompactCells[30]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell31 : phiCompactCellPass phiCompactCells[31]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell32 : phiCompactCellPass phiCompactCells[32]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell33 : phiCompactCellPass phiCompactCells[33]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell34 : phiCompactCellPass phiCompactCells[34]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 30 through 34. -/
theorem phiCompactReplay06 :
    ((phiCompactCells.drop 30).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 30).take 5 =
      [phiCompactCells[30]!, phiCompactCells[31]!, phiCompactCells[32]!, phiCompactCells[33]!, phiCompactCells[34]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell30, cell31, cell32, cell33, cell34, Bool.true_and]

end Nuttall
