import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell7Data

namespace Nuttall

open W5

def psiTwoCell7Corner : FixedIntInterval := ⟨3084807488528464789917533, 3084807488528669455556672⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[20513, 0, 0, 0, 0, 0, 0, 0],
  #v[38237, 41145, 0, 0, 0, 0, 0, 0],
  #v[51318, 93810, 58304, 0, 0, 0, 0, 0],
  #v[57574, 141437, 139072, 68004, 0, 0, 0, 0],
  #v[53578, 161615, 214787, 150615, 68182, 0, 0, 0],
  #v[42191, 145196, 227808, 220006, 118571, 57051, 0, 0],
  #v[44832, 165779, 285160, 290498, 219263, 85168, 43781, 0],
  #v[80797, 333840, 642770, 769523, 596094, 369305, 114817, 49949]
]

def psiTwoCell7Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell7Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell7Basis psiOneCell7Snapshot.corner psiTwoCell7Corner
      psiOneCell7Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell7Margin_checked

end Nuttall
