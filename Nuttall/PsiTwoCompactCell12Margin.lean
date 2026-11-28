import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell12Data

namespace Nuttall

open W5

def psiTwoCell12Corner : FixedIntInterval := ⟨1639678683886723615685259, 1639678683886923084494917⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[28137, 0, 0, 0, 0, 0, 0, 0],
  #v[57289, 52203, 0, 0, 0, 0, 0, 0],
  #v[83634, 133243, 68491, 0, 0, 0, 0, 0],
  #v[100727, 218298, 187152, 73535, 0, 0, 0, 0],
  #v[103731, 276571, 319677, 196135, 67961, 0, 0, 0],
  #v[97502, 300326, 417610, 342365, 165907, 55591, 0, 0],
  #v[96602, 333201, 530972, 507208, 330450, 129221, 44033, 0],
  #v[97034, 386573, 719714, 830731, 631584, 369019, 118348, 44639]
]

def psiTwoCell12Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell12Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell12Basis psiOneCell12Snapshot.corner psiTwoCell12Corner
      psiOneCell12Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell12Margin_checked

end Nuttall
