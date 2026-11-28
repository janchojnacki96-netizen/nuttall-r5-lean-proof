import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell30Data

namespace Nuttall

open W5

def psiTwoCell30Corner : FixedIntInterval := ⟨56735291266828816780056, 56735291267009799750112⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[151260, 0, 0, 0, 0, 0, 0, 0],
  #v[418411, 211924, 0, 0, 0, 0, 0, 0],
  #v[821847, 776629, 209965, 0, 0, 0, 0, 0],
  #v[1322032, 1764342, 878740, 169855, 0, 0, 0, 0],
  #v[1846031, 3112579, 2171877, 761377, 119000, 0, 0, 0],
  #v[2310121, 4636237, 4063190, 1978039, 549817, 74574, 0, 0],
  #v[2642203, 6083471, 6317901, 3838673, 1467856, 345389, 42655, 0],
  #v[2803622, 7222351, 8573193, 6143015, 2911242, 933289, 193642, 22589]
]

def psiTwoCell30Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell30Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell30Basis psiOneCell30Snapshot.corner psiTwoCell30Corner
      psiOneCell30Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell30Margin_checked

end Nuttall
