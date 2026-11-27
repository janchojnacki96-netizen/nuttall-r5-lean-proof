import Nuttall.PhiCompactCells

namespace Nuttall

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
private theorem cell50 : phiCompactCellPass phiCompactCells[50]! = true := by
  decide +kernel

/-- Kernel certificate for compact cell indices 50 through 50. -/
theorem phiCompactReplay10 :
    ((phiCompactCells.drop 50).take 1).all phiCompactCellPass = true := by
  have h : (phiCompactCells.drop 50).take 1 =
      [phiCompactCells[50]!] := by decide +kernel
  simp only [h, List.all_cons, List.all_nil, cell50, Bool.true_and]

end Nuttall
