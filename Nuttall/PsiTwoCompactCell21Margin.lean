import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell21Data

namespace Nuttall

open W5

def psiTwoCell21Corner : FixedIntInterval := ⟨389687634778871380775534, 389687634779061572007954⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[57715, 0, 0, 0, 0, 0, 0, 0],
  #v[137236, 93059, 0, 0, 0, 0, 0, 0],
  #v[232521, 286481, 106113, 0, 0, 0, 0, 0],
  #v[323218, 552657, 363119, 98808, 0, 0, 0, 0],
  #v[390115, 831400, 749469, 350417, 79644, 0, 0, 0],
  #v[423915, 1063106, 1183692, 750308, 280420, 57497, 0, 0],
  #v[419822, 1198375, 1563456, 1213687, 610003, 193728, 37971, 0],
  #v[372513, 1182022, 1748358, 1584565, 965738, 413040, 115307, 22842]
]

def psiTwoCell21Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell21Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell21Basis psiOneCell21Snapshot.corner psiTwoCell21Corner
      psiOneCell21Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell21Margin_checked

end Nuttall
