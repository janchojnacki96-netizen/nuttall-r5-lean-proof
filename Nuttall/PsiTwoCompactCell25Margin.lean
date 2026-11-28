import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell25Data

namespace Nuttall

open W5

def psiTwoCell25Corner : FixedIntInterval := ⟨177300068760883367962852, 177300068761069456484221⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[85565, 0, 0, 0, 0, 0, 0, 0],
  #v[217694, 129614, 0, 0, 0, 0, 0, 0],
  #v[393942, 431725, 138846, 0, 0, 0, 0, 0],
  #v[584339, 895994, 520931, 121449, 0, 0, 0, 0],
  #v[752737, 1447596, 1165855, 480134, 91994, 0, 0, 0],
  #v[870039, 1979575, 1984985, 1120306, 367852, 62351, 0, 0],
  #v[917539, 2383843, 2814390, 1962769, 874331, 244031, 38561, 0],
  #v[894905, 2589438, 3474327, 2836647, 1547140, 580913, 143111, 22001]
]

def psiTwoCell25Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell25Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell25Basis psiOneCell25Snapshot.corner psiTwoCell25Corner
      psiOneCell25Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell25Margin_checked

end Nuttall
