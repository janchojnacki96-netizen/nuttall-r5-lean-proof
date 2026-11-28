import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell9Data

namespace Nuttall

open W5

def psiTwoCell9Corner : FixedIntInterval := ⟨2425968495510896724254179, 2425968495511099306700984⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[23132, 0, 0, 0, 0, 0, 0, 0],
  #v[44677, 44972, 0, 0, 0, 0, 0, 0],
  #v[62029, 107379, 61805, 0, 0, 0, 0, 0],
  #v[71485, 167142, 155796, 69702, 0, 0, 0, 0],
  #v[69300, 198933, 249897, 166525, 67510, 0, 0, 0],
  #v[59787, 196641, 293679, 264170, 137149, 56296, 0, 0],
  #v[62341, 225046, 376681, 376360, 266554, 105802, 45020, 0],
  #v[127579, 521772, 995239, 1178359, 909788, 551871, 174844, 71869]
]

def psiTwoCell9Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell9Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell9Basis psiOneCell9Snapshot.corner psiTwoCell9Corner
      psiOneCell9Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell9Margin_checked

end Nuttall
