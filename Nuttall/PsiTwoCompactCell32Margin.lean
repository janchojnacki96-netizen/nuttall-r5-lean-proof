import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell32Data

namespace Nuttall

open W5

def psiTwoCell32Corner : FixedIntInterval := ⟨34074686238957665098857, 34074686239136603040908⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[195179, 0, 0, 0, 0, 0, 0, 0],
  #v[558132, 265050, 0, 0, 0, 0, 0, 0],
  #v[1132720, 1008336, 254523, 0, 0, 0, 0, 0],
  #v[1882083, 2374297, 1111125, 199568, 0, 0, 0, 0],
  #v[2714017, 4337555, 2855821, 938271, 135516, 0, 0, 0],
  #v[3506690, 6686056, 5546885, 2543377, 660919, 82309, 0, 0],
  #v[4141591, 9076619, 8946156, 5138810, 1847463, 405490, 45634, 0],
  #v[4536018, 11142006, 12580006, 8546957, 3824996, 1150815, 222361, 23426]
]

def psiTwoCell32Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell32Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell32Basis psiOneCell32Snapshot.corner psiTwoCell32Corner
      psiOneCell32Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell32Margin_checked

end Nuttall
