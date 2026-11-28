import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell20Data

namespace Nuttall

open W5

def psiTwoCell20Corner : FixedIntInterval := ⟨467178047795478582710516, 467178047795669797635272⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[52712, 0, 0, 0, 0, 0, 0, 0],
  #v[123223, 86328, 0, 0, 0, 0, 0, 0],
  #v[205365, 260478, 99987, 0, 0, 0, 0, 0],
  #v[280877, 493365, 334131, 94572, 0, 0, 0, 0],
  #v[333460, 728891, 675650, 325950, 77416, 0, 0, 0],
  #v[356963, 916782, 1047310, 683190, 263499, 56776, 0, 0],
  #v[348726, 1018703, 1361996, 1085273, 562040, 183993, 38170, 0],
  #v[299871, 974410, 1477910, 1376011, 862435, 381714, 109616, 23286]
]

def psiTwoCell20Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell20Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell20Basis psiOneCell20Snapshot.corner psiTwoCell20Corner
      psiOneCell20Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell20Margin_checked

end Nuttall
