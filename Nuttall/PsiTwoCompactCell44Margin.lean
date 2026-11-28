import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell44Data

namespace Nuttall

open W5

def psiTwoCell44Corner : FixedIntInterval := ⟨723203179234948656848, 723203179401734196089⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[1339737, 0, 0, 0, 0, 0, 0, 0],
  #v[4664830, 1508397, 0, 0, 0, 0, 0, 0],
  #v[11504402, 7127507, 1200886, 0, 0, 0, 0, 0],
  #v[23197846, 20722379, 6657126, 780631, 0, 0, 0, 0],
  #v[40557454, 46561630, 21485563, 4777222, 439464, 0, 0, 0],
  #v[63485841, 88020376, 52039624, 16550760, 2868548, 221283, 0, 0],
  #v[90797662, 146241742, 104151503, 42300257, 10438580, 1505981, 101714, 0],
  #v[120319601, 219254426, 181008598, 88317222, 27732443, 5667888, 709830, 43286]
]

def psiTwoCell44Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell44Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell44Basis psiOneCell44Snapshot.corner psiTwoCell44Corner
      psiOneCell44Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell44Margin_checked

end Nuttall
