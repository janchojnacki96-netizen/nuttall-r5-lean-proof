import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell47Data

namespace Nuttall

open W5

def psiTwoCell47Corner : FixedIntInterval := ⟨214161951220187589715, 214161951383964517495⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[2461946, 0, 0, 0, 0, 0, 0, 0],
  #v[9000076, 2644973, 0, 0, 0, 0, 0, 0],
  #v[23296858, 13172133, 2009336, 0, 0, 0, 0, 0],
  #v[49295556, 40327204, 11788317, 1246353, 0, 0, 0, 0],
  #v[90423779, 95355880, 40201954, 8108561, 669517, 0, 0, 0],
  #v[148484435, 189602953, 102772202, 29791889, 4668881, 321684, 0, 0],
  #v[222751865, 331206969, 216903427, 80609849, 18086751, 2351561, 141093, 0],
  #v[309589046, 521913935, 397243434, 177947731, 51031714, 9459438, 1063933, 57295]
]

def psiTwoCell47Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell47Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell47Basis psiOneCell47Snapshot.corner psiTwoCell47Corner
      psiOneCell47Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell47Margin_checked

end Nuttall
