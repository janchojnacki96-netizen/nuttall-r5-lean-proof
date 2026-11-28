import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiTwoCompactPointRow
import Nuttall.PsiCompactCell3Data

namespace Nuttall

open W5

def psiTwoCell3Corner : FixedIntInterval := ⟨4765142304456726977533027, 4765142304456935808199647⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[16505, 0, 0, 0, 0, 0, 0, 0],
  #v[28632, 35241, 0, 0, 0, 0, 0, 0],
  #v[35836, 72870, 53019, 0, 0, 0, 0, 0],
  #v[38444, 103870, 112761, 66264, 0, 0, 0, 0],
  #v[33489, 111610, 166385, 127140, 72623, 0, 0, 0],
  #v[18459, 71015, 125333, 148391, 82725, 60712, 0, 0],
  #v[20263, 76599, 136350, 134743, 125974, 35711, 38304, 0],
  #v[32703, 140385, 279176, 350964, 266646, 186340, 47040, 28891]
]

def psiTwoCell3Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell3Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell3Basis psiOneCell3Snapshot.corner psiTwoCell3Corner
      psiOneCell3Snapshot.jets j < psiTwoCompactThreshold := by
  rw [← psiTwoCompactPointRow_eq]
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell3Margin_checked

end Nuttall
