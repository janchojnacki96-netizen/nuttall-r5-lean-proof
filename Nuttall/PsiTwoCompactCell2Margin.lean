import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell2Data

namespace Nuttall

open W5

def psiTwoCell2Corner : FixedIntInterval := ⟨5265579714745738175637465, 5265579714745948047221315⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[15701, 0, 0, 0, 0, 0, 0, 0],
  #v[26749, 34054, 0, 0, 0, 0, 0, 0],
  #v[32876, 68620, 51985, 0, 0, 0, 0, 0],
  #v[34953, 96622, 107297, 66109, 0, 0, 0, 0],
  #v[30211, 103197, 158333, 123027, 74584, 0, 0, 0],
  #v[14225, 57015, 104743, 134189, 74222, 62663, 0, 0],
  #v[16068, 60280, 107058, 100232, 104455, 21684, 36551, 0],
  #v[27985, 121672, 244283, 312844, 233453, 171552, 38396, 27322]
]

def psiTwoCell2Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell2Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell2Basis psiOneCell2Snapshot.corner psiTwoCell2Corner
      psiOneCell2Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell2Margin_checked

end Nuttall
