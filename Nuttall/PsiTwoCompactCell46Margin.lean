import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell46Data

namespace Nuttall

open W5

def psiTwoCell46Corner : FixedIntInterval := ⟨325503286292581489939, 325503286457361259341⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[1996972, 0, 0, 0, 0, 0, 0, 0],
  #v[7182866, 2179211, 0, 0, 0, 0, 0, 0],
  #v[18295614, 10664904, 1681573, 0, 0, 0, 0, 0],
  #v[38096565, 32095014, 9681861, 1059471, 0, 0, 0, 0],
  #v[68772204, 74612827, 32419654, 6754738, 578090, 0, 0, 0],
  #v[111143109, 145883734, 81404121, 24339206, 3944391, 282130, 0, 0],
  #v[164100640, 250618666, 168798206, 64621157, 14967010, 2014483, 125693, 0],
  #v[224478416, 388428378, 303798207, 140034654, 41394869, 7927133, 924037, 51845]
]

def psiTwoCell46Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell46Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell46Basis psiOneCell46Snapshot.corner psiTwoCell46Corner
      psiOneCell46Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell46Margin_checked

end Nuttall
