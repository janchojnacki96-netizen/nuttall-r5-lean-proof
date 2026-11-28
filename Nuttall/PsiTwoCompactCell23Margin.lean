import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell23Data

namespace Nuttall

open W5

def psiTwoCell23Corner : FixedIntInterval := ⟨266238672000027688782501, 266238672000215832801069⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[69826, 0, 0, 0, 0, 0, 0, 0],
  #v[171758, 109126, 0, 0, 0, 0, 0, 0],
  #v[300758, 349542, 120608, 0, 0, 0, 0, 0],
  #v[431865, 699450, 432394, 108845, 0, 0, 0, 0],
  #v[538571, 1090626, 929492, 407988, 85055, 0, 0, 0],
  #v[603382, 1441860, 1524096, 911832, 319620, 59494, 0, 0],
  #v[616078, 1678241, 2083521, 1533705, 725816, 216366, 37991, 0],
  #v[576221, 1745541, 2458311, 2113890, 1218690, 487889, 128197, 22267]
]

def psiTwoCell23Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell23Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell23Basis psiOneCell23Snapshot.corner psiTwoCell23Corner
      psiOneCell23Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell23Margin_checked

end Nuttall
