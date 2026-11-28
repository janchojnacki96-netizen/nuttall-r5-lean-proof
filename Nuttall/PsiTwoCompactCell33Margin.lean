import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell33Data

namespace Nuttall

open W5

def psiTwoCell33Corner : FixedIntInterval := ⟨26077003989579363215716, 26077003989757287847328⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[223111, 0, 0, 0, 0, 0, 0, 0],
  #v[648657, 298286, 0, 0, 0, 0, 0, 0],
  #v[1338103, 1156018, 281999, 0, 0, 0, 0, 0],
  #v[2259607, 2771039, 1256950, 217684, 0, 0, 0, 0],
  #v[3311243, 5151313, 3294033, 1047654, 145527, 0, 0, 0],
  #v[4347348, 8077476, 6518686, 2900398, 728686, 87018, 0, 0],
  #v[5217262, 11152937, 10706673, 5978660, 2083843, 441673, 47498, 0],
  #v[5805267, 13920916, 15325206, 10136363, 4407225, 1284417, 239423, 24005]
]

def psiTwoCell33Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell33Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell33Basis psiOneCell33Snapshot.corner psiTwoCell33Corner
      psiOneCell33Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell33Margin_checked

end Nuttall
