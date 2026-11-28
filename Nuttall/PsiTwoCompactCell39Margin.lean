import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell39Data

namespace Nuttall

open W5

def psiTwoCell39Corner : FixedIntInterval := ⟨4316462235983809489196, 4316462236155653410158⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[548385, 0, 0, 0, 0, 0, 0, 0],
  #v[1759805, 667577, 0, 0, 0, 0, 0, 0],
  #v[4002539, 2886116, 574660, 0, 0, 0, 0, 0],
  #v[7446643, 7691769, 2891382, 403906, 0, 0, 0, 0],
  #v[12016409, 15863778, 8499486, 2223744, 245858, 0, 0, 0],
  #v[17365567, 27554556, 18794984, 6969810, 1429727, 133856, 0, 0],
  #v[22934427, 42097663, 34403606, 16173472, 4673572, 802812, 66527, 0],
  #v[28069256, 58075506, 54760482, 30740045, 11209460, 2694204, 404193, 30612]
]

def psiTwoCell39Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell39Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell39Basis psiOneCell39Snapshot.corner psiTwoCell39Corner
      psiOneCell39Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell39Margin_checked

end Nuttall
