import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell4Data

namespace Nuttall

open W5

def psiTwoCell4Corner : FixedIntInterval := ⟨4297510627101388755052362, 4297510627101596533142643⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[17380, 0, 0, 0, 0, 0, 0, 0],
  #v[30699, 36532, 0, 0, 0, 0, 0, 0],
  #v[39113, 77470, 54158, 0, 0, 0, 0, 0],
  #v[42378, 111866, 118611, 66519, 0, 0, 0, 0],
  #v[37379, 121516, 175997, 131968, 71045, 0, 0, 0],
  #v[23275, 86630, 147794, 164171, 91463, 59325, 0, 0],
  #v[25171, 95158, 168681, 170883, 148245, 48936, 39900, 0],
  #v[39350, 166955, 328936, 406936, 312763, 209488, 57721, 31366]
]

def psiTwoCell4Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell4Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell4Basis psiOneCell4Snapshot.corner psiTwoCell4Corner
      psiOneCell4Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell4Margin_checked

end Nuttall
