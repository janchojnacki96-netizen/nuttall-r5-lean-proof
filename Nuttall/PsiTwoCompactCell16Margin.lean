import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell16Data

namespace Nuttall

open W5

def psiTwoCell16Corner : FixedIntInterval := ⟨912030190907625568139401, 912030190907820903082459⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[37726, 0, 0, 0, 0, 0, 0, 0],
  #v[82344, 65764, 0, 0, 0, 0, 0, 0],
  #v[128460, 182801, 81075, 0, 0, 0, 0, 0],
  #v[164724, 321790, 245625, 81661, 0, 0, 0, 0],
  #v[182684, 441338, 456972, 249281, 71058, 0, 0, 0],
  #v[184309, 519423, 655930, 479451, 208575, 55377, 0, 0],
  #v[175080, 559057, 821170, 722435, 420878, 153376, 40396, 0],
  #v[132116, 476217, 804460, 839993, 588840, 302066, 94799, 27326]
]

def psiTwoCell16Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell16Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell16Basis psiOneCell16Snapshot.corner psiTwoCell16Corner
      psiOneCell16Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell16Margin_checked

end Nuttall
