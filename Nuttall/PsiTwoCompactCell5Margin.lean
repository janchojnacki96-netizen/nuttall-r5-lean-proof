import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiTwoCompactPointRow
import Nuttall.PsiCompactCell5Data

namespace Nuttall

open W5

def psiTwoCell5Corner : FixedIntInterval := ⟨3862087583202036140319501, 3862087583202242880869021⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[18333, 0, 0, 0, 0, 0, 0, 0],
  #v[32971, 37939, 0, 0, 0, 0, 0, 0],
  #v[42752, 82460, 55410, 0, 0, 0, 0, 0],
  #v[46823, 120714, 124906, 66887, 0, 0, 0, 0],
  #v[41961, 133045, 187220, 137496, 69804, 0, 0, 0],
  #v[28765, 104049, 172249, 181401, 100374, 58327, 0, 0],
  #v[30869, 116156, 204277, 208930, 171338, 61562, 41366, 0],
  #v[48674, 204380, 399168, 487211, 376743, 243914, 71358, 35174]
]

def psiTwoCell5Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell5Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell5Basis psiOneCell5Snapshot.corner psiTwoCell5Corner
      psiOneCell5Snapshot.jets j < psiTwoCompactThreshold := by
  rw [← psiTwoCompactPointRow_eq]
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell5Margin_checked

end Nuttall
