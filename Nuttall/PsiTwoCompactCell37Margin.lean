import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell37Data

namespace Nuttall

open W5

def psiTwoCell37Corner : FixedIntInterval := ⟨8172773450459690939915, 8172773450633554389250⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[398534, 0, 0, 0, 0, 0, 0, 0],
  #v[1237645, 500550, 0, 0, 0, 0, 0, 0],
  #v[2724963, 2087295, 444555, 0, 0, 0, 0, 0],
  #v[4908786, 5370775, 2149607, 322378, 0, 0, 0, 0],
  #v[7670897, 10701320, 6083698, 1698792, 202460, 0, 0, 0],
  #v[10736718, 17965932, 12966912, 5111115, 1121747, 113727, 0, 0],
  #v[13734767, 26539670, 22896861, 11404792, 3509076, 646522, 58317, 0],
  #v[16283921, 35411621, 35180058, 20869766, 8073695, 2069835, 333872, 27686]
]

def psiTwoCell37Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell37Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell37Basis psiOneCell37Snapshot.corner psiTwoCell37Corner
      psiOneCell37Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell37Margin_checked

end Nuttall
