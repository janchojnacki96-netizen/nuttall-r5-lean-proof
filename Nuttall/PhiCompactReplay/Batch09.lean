import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell45 : phiCompactCellPass phiCompactCells[45]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell46 : phiCompactCellPass phiCompactCells[46]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell47 : phiCompactCellPass phiCompactCells[47]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell48 : phiCompactCellPass phiCompactCells[48]! = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell49 : phiCompactCellPass phiCompactCells[49]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 45 through 49. -/
theorem phiCompactReplay09 :
    ((phiCompactCells.drop 45).take 5).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 45).take 5 =
      [phiCompactCells[45]!, phiCompactCells[46]!, phiCompactCells[47]!, phiCompactCells[48]!, phiCompactCells[49]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell45, cell46, cell47, cell48, cell49, Bool.true_and]

end Nuttall
