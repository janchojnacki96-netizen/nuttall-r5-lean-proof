import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell1Data

namespace Nuttall

open W5

def psiTwoCell1Corner : FixedIntInterval := ⟨5799276949889803173834941, 5799276949890014086336800⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[14961, 0, 0, 0, 0, 0, 0, 0],
  #v[25029, 32962, 0, 0, 0, 0, 0, 0],
  #v[30198, 64682, 51047, 0, 0, 0, 0, 0],
  #v[31846, 90031, 102168, 66040, 0, 0, 0, 0],
  #v[27479, 96163, 151800, 119648, 76975, 0, 0, 0],
  #v[10496, 44475, 85948, 121810, 66066, 65461, 0, 0],
  #v[12510, 45963, 80467, 66861, 83459, 6510, 34558, 0],
  #v[24724, 108956, 220840, 288754, 210310, 163496, 31302, 26408]
]

def psiTwoCell1Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell1Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell1Basis psiOneCell1Snapshot.corner psiTwoCell1Corner
      psiOneCell1Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell1Margin_checked

end Nuttall
