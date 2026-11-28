import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell0Data

namespace Nuttall

open W5

def psiTwoCell0Corner : FixedIntInterval := ⟨6366539749957945036733125, 6366539749958156990238144⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[14279, 0, 0, 0, 0, 0, 0, 0],
  #v[23457, 31959, 0, 0, 0, 0, 0, 0],
  #v[27769, 61025, 50197, 0, 0, 0, 0, 0],
  #v[29072, 84014, 97323, 66043, 0, 0, 0, 0],
  #v[25234, 90405, 146749, 117018, 79844, 0, 0, 0],
  #v[7203, 33280, 68963, 111730, 58467, 69593, 0, 0],
  #v[9520, 33421, 56206, 33954, 62628, -10353, 32188, 0],
  #v[22602, 100998, 206615, 276293, 195473, 161244, 25520, 26001]
]

def psiTwoCell0Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell0Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell0Basis psiOneCell0Snapshot.corner psiTwoCell0Corner
      psiOneCell0Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell0Margin_checked

end Nuttall
