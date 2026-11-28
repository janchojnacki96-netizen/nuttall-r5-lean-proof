import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiTwoCompactPointRow
import Nuttall.PsiCompactCell10Data

namespace Nuttall

open W5

def psiTwoCell10Corner : FixedIntInterval := ⟨2138199251622436523753277, 2138199251622638072206931⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[24639, 0, 0, 0, 0, 0, 0, 0],
  #v[48436, 47162, 0, 0, 0, 0, 0, 0],
  #v[68387, 115174, 63823, 0, 0, 0, 0, 0],
  #v[79946, 182294, 165316, 70796, 0, 0, 0, 0],
  #v[79107, 221554, 270659, 175583, 67478, 0, 0, 0],
  #v[70595, 227144, 331208, 288493, 146585, 56018, 0, 0],
  #v[72509, 258127, 425514, 419595, 288807, 114611, 45049, 0],
  #v[125294, 509846, 967980, 1140269, 878139, 528267, 168129, 67708]
]

def psiTwoCell10Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell10Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell10Basis psiOneCell10Snapshot.corner psiTwoCell10Corner
      psiOneCell10Snapshot.jets j < psiTwoCompactThreshold := by
  rw [← psiTwoCompactPointRow_eq]
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell10Margin_checked

end Nuttall
