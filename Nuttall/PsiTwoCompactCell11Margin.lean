import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell11Data

namespace Nuttall

open W5

def psiTwoCell11Corner : FixedIntInterval := ⟨1876544751160438374059241, 1876544751160638888520542⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[26301, 0, 0, 0, 0, 0, 0, 0],
  #v[52621, 49564, 0, 0, 0, 0, 0, 0],
  #v[75549, 123761, 66044, 0, 0, 0, 0, 0],
  #v[89627, 199261, 175731, 72069, 0, 0, 0, 0],
  #v[90495, 247287, 293833, 185433, 67630, 0, 0, 0],
  #v[83062, 261491, 372340, 314487, 156154, 55785, 0, 0],
  #v[83818, 293893, 476612, 462975, 309981, 122367, 44694, 0],
  #v[108720, 438915, 827260, 967036, 741363, 440885, 140903, 55250]
]

def psiTwoCell11Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell11Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell11Basis psiOneCell11Snapshot.corner psiTwoCell11Corner
      psiOneCell11Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell11Margin_checked

end Nuttall
