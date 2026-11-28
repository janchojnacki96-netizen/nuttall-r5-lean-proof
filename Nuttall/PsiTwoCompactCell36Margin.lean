import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell36Data

namespace Nuttall

open W5

def psiTwoCell36Corner : FixedIntInterval := ⟨11078192064684328633964, 11078192064859201934010⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[342307, 0, 0, 0, 0, 0, 0, 0],
  #v[1045696, 436697, 0, 0, 0, 0, 0, 0],
  #v[2265203, 1788235, 393952, 0, 0, 0, 0, 0],
  #v[4015216, 4520809, 1867004, 290180, 0, 0, 0, 0],
  #v[6174562, 8853315, 5183933, 1495442, 185109, 0, 0, 0],
  #v[8505208, 14612258, 10846839, 4407449, 1000568, 105618, 0, 0],
  #v[10707973, 21224765, 18810782, 9642814, 3061235, 584128, 55012, 0],
  #v[12495291, 27851488, 28395128, 17312920, 6897453, 1826079, 305424, 26528]
]

def psiTwoCell36Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell36Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell36Basis psiOneCell36Snapshot.corner psiTwoCell36Corner
      psiOneCell36Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell36Margin_checked

end Nuttall
