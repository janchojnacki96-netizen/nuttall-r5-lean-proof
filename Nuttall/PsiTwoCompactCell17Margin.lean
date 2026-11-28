import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell17Data

namespace Nuttall

open W5

def psiTwoCell17Corner : FixedIntInterval := ⟨777870451515046185574557, 777870451515240493363682⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[40850, 0, 0, 0, 0, 0, 0, 0],
  #v[90712, 70107, 0, 0, 0, 0, 0, 0],
  #v[143876, 198968, 85092, 0, 0, 0, 0, 0],
  #v[187472, 356701, 264322, 84366, 0, 0, 0, 0],
  #v[211572, 498587, 502220, 265784, 72308, 0, 0, 0],
  #v[216677, 596857, 735348, 522477, 220768, 55535, 0, 0],
  #v[206117, 644149, 924921, 794698, 449746, 159987, 39630, 0],
  #v[159616, 559731, 919334, 931910, 635591, 313826, 96805, 25788]
]

def psiTwoCell17Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell17Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell17Basis psiOneCell17Snapshot.corner psiTwoCell17Corner
      psiOneCell17Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell17Margin_checked

end Nuttall
