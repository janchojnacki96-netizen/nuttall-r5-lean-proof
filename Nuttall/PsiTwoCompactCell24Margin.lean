import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell24Data

namespace Nuttall

open W5

def psiTwoCell24Corner : FixedIntInterval := ⟨217983350255544337570346, 217983350255731446322309⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[77168, 0, 0, 0, 0, 0, 0, 0],
  #v[193052, 118734, 0, 0, 0, 0, 0, 0],
  #v[343653, 387853, 129193, 0, 0, 0, 0, 0],
  #v[501536, 790411, 473884, 114785, 0, 0, 0, 0],
  #v[635695, 1254578, 1039457, 441971, 88311, 0, 0, 0],
  #v[723338, 1686796, 1736755, 1009270, 342445, 60805, 0, 0],
  #v[750522, 1996776, 2417614, 1732376, 795433, 229498, 38207, 0],
  #v[717593, 2124513, 2920371, 2446883, 1372107, 531889, 135381, 22100]
]

def psiTwoCell24Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell24Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell24Basis psiOneCell24Snapshot.corner psiTwoCell24Corner
      psiOneCell24Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell24Margin_checked

end Nuttall
