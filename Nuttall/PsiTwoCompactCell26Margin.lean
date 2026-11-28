import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell26Data

namespace Nuttall

open W5

def psiTwoCell26Corner : FixedIntInterval := ⟨143230986962948192911951, 143230986963133261287455⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[95199, 0, 0, 0, 0, 0, 0, 0],
  #v[246310, 141974, 0, 0, 0, 0, 0, 0],
  #v[453106, 482133, 149730, 0, 0, 0, 0, 0],
  #v[683095, 1018965, 574453, 128938, 0, 0, 0, 0],
  #v[894289, 1675622, 1311632, 523133, 96155, 0, 0, 0],
  #v[1050079, 2330735, 2275695, 1247243, 396230, 64155, 0, 0],
  #v[1125629, 2855466, 3286778, 2230548, 963895, 260143, 39058, 0],
  #v[1118173, 3161983, 4140876, 3294425, 1747503, 635673, 151468, 21971]
]

def psiTwoCell26Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell26Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell26Basis psiOneCell26Snapshot.corner psiTwoCell26Corner
      psiOneCell26Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell26Margin_checked

end Nuttall
