import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell15Data

namespace Nuttall

open W5

def psiTwoCell15Corner : FixedIntInterval := ⟨1063843644946591917395571, 1063843644946788294528206⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[34931, 0, 0, 0, 0, 0, 0, 0],
  #v[74936, 61848, 0, 0, 0, 0, 0, 0],
  #v[114984, 168345, 77445, 0, 0, 0, 0, 0],
  #v[145114, 291007, 228762, 79250, 0, 0, 0, 0],
  #v[158091, 391494, 416668, 234214, 70009, 0, 0, 0],
  #v[157037, 452666, 585755, 440479, 197131, 55319, 0, 0],
  #v[149695, 488038, 732734, 659365, 395275, 147229, 41274, 0],
  #v[112260, 416192, 723167, 777653, 559435, 298052, 94733, 29514]
]

def psiTwoCell15Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell15Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell15Basis psiOneCell15Snapshot.corner psiTwoCell15Corner
      psiOneCell15Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell15Margin_checked

end Nuttall
