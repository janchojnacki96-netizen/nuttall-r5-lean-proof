import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell22Data

namespace Nuttall

open W5

def psiTwoCell22Corner : FixedIntInterval := ⟨323102594556848273281134, 323102594557037440906333⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[63384, 0, 0, 0, 0, 0, 0, 0],
  #v[153295, 100617, 0, 0, 0, 0, 0, 0],
  #v[264046, 315979, 112953, 0, 0, 0, 0, 0],
  #v[373044, 620829, 395689, 103544, 0, 0, 0, 0],
  #v[457693, 950890, 833512, 377628, 82178, 0, 0, 0],
  #v[504954, 1236261, 1341313, 826058, 299042, 58397, 0, 0],
  #v[507576, 1415498, 1801641, 1362094, 664325, 204484, 37912, 0],
  #v[463141, 1435715, 2071878, 1828764, 1083969, 448384, 121511, 22510]
]

def psiTwoCell22Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell22Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell22Basis psiOneCell22Snapshot.corner psiTwoCell22Corner
      psiOneCell22Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell22Margin_checked

end Nuttall
