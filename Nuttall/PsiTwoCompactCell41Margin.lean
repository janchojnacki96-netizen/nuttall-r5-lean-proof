import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell41Data

namespace Nuttall

open W5

def psiTwoCell41Corner : FixedIntInterval := ⟨2185568175046409350152, 2185568175216225459010⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[770668, 0, 0, 0, 0, 0, 0, 0],
  #v[2555354, 909318, 0, 0, 0, 0, 0, 0],
  #v[6003483, 4074429, 758676, 0, 0, 0, 0, 0],
  #v[11535166, 11244894, 3969717, 516840, 0, 0, 0, 0],
  #v[19220723, 24002717, 12116611, 2970275, 304922, 0, 0, 0],
  #v[28679147, 43130425, 27791794, 9693648, 1858686, 160905, 0, 0],
  #v[39102870, 68145796, 52727368, 23385515, 6345034, 1016305, 77511, 0],
  #v[49403793, 97195275, 86936482, 46156847, 15858474, 3572692, 498554, 34569]
]

def psiTwoCell41Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell41Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell41Basis psiOneCell41Snapshot.corner psiTwoCell41Corner
      psiOneCell41Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell41Margin_checked

end Nuttall
