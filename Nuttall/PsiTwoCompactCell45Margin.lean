import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell45Data

namespace Nuttall

open W5

def psiTwoCell45Corner : FixedIntInterval := ⟨488280763628163645337, 488280763793946257064⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[1630478, 0, 0, 0, 0, 0, 0, 0],
  #v[5770192, 1807285, 0, 0, 0, 0, 0, 0],
  #v[14462118, 8691212, 1416537, 0, 0, 0, 0, 0],
  #v[29634332, 25708756, 8003261, 906540, 0, 0, 0, 0],
  #v[52646757, 58758417, 26311056, 5663036, 502433, 0, 0, 0],
  #v[83735675, 112966395, 64887741, 20009837, 3353466, 249068, 0, 0],
  #v[121681351, 190853601, 132189695, 52126302, 12462153, 1736532, 112711, 0],
  #v[163827762, 290931274, 233791867, 110879273, 33782644, 6683437, 807486, 47222]
]

def psiTwoCell45Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell45Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell45Basis psiOneCell45Snapshot.corner psiTwoCell45Corner
      psiOneCell45Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell45Margin_checked

end Nuttall
