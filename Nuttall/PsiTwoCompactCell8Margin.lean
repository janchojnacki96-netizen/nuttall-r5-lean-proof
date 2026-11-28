import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiTwoCompactPointRow
import Nuttall.PsiCompactCell8Data

namespace Nuttall

open W5

def psiTwoCell8Corner : FixedIntInterval := ⟨2741111766345728435032902, 2741111766345932051558086⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[21761, 0, 0, 0, 0, 0, 0, 0],
  #v[41292, 42973, 0, 0, 0, 0, 0, 0],
  #v[56369, 100284, 59971, 0, 0, 0, 0, 0],
  #v[64076, 153586, 147076, 68775, 0, 0, 0, 0],
  #v[60852, 179056, 231332, 158213, 67739, 0, 0, 0],
  #v[50387, 169466, 259325, 241373, 127815, 56631, 0, 0],
  #v[53137, 194272, 329818, 333191, 243251, 95944, 44586, 0],
  #v[105968, 435384, 833985, 992240, 767514, 469658, 147812, 62163]
]

def psiTwoCell8Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell8Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell8Basis psiOneCell8Snapshot.corner psiTwoCell8Corner
      psiOneCell8Snapshot.jets j < psiTwoCompactThreshold := by
  rw [← psiTwoCompactPointRow_eq]
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell8Margin_checked

end Nuttall
