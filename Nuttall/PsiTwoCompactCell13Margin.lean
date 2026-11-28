import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell13Data

namespace Nuttall

open W5

def psiTwoCell13Corner : FixedIntInterval := ⟨1426221989554838027452410, 1426221989555036465646061⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[30169, 0, 0, 0, 0, 0, 0, 0],
  #v[62509, 55108, 0, 0, 0, 0, 0, 0],
  #v[92786, 143739, 71187, 0, 0, 0, 0, 0],
  #v[113479, 239696, 199699, 75208, 0, 0, 0, 0],
  #v[119136, 309930, 348504, 207766, 68466, 0, 0, 0],
  #v[114303, 344444, 467691, 372407, 175921, 55441, 0, 0],
  #v[111367, 377409, 590265, 553565, 350909, 135438, 43172, 0],
  #v[94266, 368248, 673103, 762475, 571929, 325908, 104655, 37443]
]

def psiTwoCell13Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell13Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell13Basis psiOneCell13Snapshot.corner psiTwoCell13Corner
      psiOneCell13Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell13Margin_checked

end Nuttall
