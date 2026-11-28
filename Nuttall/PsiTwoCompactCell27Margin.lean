import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell27Data

namespace Nuttall

open W5

def psiTwoCell27Corner : FixedIntInterval := ⟨114898346382121126668422, 114898346382305174898422⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[106290, 0, 0, 0, 0, 0, 0, 0],
  #v[279656, 156060, 0, 0, 0, 0, 0, 0],
  #v[522961, 540252, 162034, 0, 0, 0, 0, 0],
  #v[801305, 1162689, 635545, 137371, 0, 0, 0, 0],
  #v[1066114, 1945965, 1480339, 571744, 100858, 0, 0, 0],
  #v[1271834, 2753390, 2617312, 1392829, 428032, 66244, 0, 0],
  #v[1385742, 3431885, 3850800, 2542611, 1065799, 278051, 39705, 0],
  #v[1400527, 3870054, 4946241, 3834277, 1977806, 697074, 160559, 22010]
]

def psiTwoCell27Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell27Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell27Basis psiOneCell27Snapshot.corner psiTwoCell27Corner
      psiOneCell27Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell27Margin_checked

end Nuttall
