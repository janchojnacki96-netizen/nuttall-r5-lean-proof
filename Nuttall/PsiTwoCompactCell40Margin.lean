import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell40Data

namespace Nuttall

open W5

def psiTwoCell40Corner : FixedIntInterval := ⟨3088221983183267854487, 3088221983354090351820⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[648329, 0, 0, 0, 0, 0, 0, 0],
  #v[2114861, 777012, 0, 0, 0, 0, 0, 0],
  #v[4888736, 3419997, 658495, 0, 0, 0, 0, 0],
  #v[9243178, 9275482, 3378950, 455656, 0, 0, 0, 0],
  #v[15156631, 19461941, 10121712, 2563342, 273059, 0, 0, 0],
  #v[22256605, 34383178, 22795975, 8198713, 1625983, 146360, 0, 0],
  #v[29866219, 53420687, 42482213, 19399180, 5432016, 901011, 71614, 0],
  #v[37138772, 74934552, 68821983, 37574174, 13300365, 3095024, 447809, 32442]
]

def psiTwoCell40Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell40Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell40Basis psiOneCell40Snapshot.corner psiTwoCell40Corner
      psiOneCell40Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell40Margin_checked

end Nuttall
