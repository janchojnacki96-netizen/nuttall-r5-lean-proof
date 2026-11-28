import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell34Data

namespace Nuttall

open W5

def psiTwoCell34Corner : FixedIntInterval := ⟨19782753939360096771410, 19782753939537008178306⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[256157, 0, 0, 0, 0, 0, 0, 0],
  #v[757145, 337161, 0, 0, 0, 0, 0, 0],
  #v[1587579, 1331005, 313810, 0, 0, 0, 0, 0],
  #v[2724595, 3247759, 1427877, 238485, 0, 0, 0, 0],
  #v[4057347, 6143430, 3815099, 1174565, 156961, 0, 0, 0],
  #v[5412831, 9799287, 7691847, 3320671, 806568, 92400, 0, 0],
  #v[6600587, 13761162, 12865085, 6982812, 2359408, 482886, 49654, 0],
  #v[7461756, 17465206, 18744097, 12067581, 5096895, 1438722, 258691, 24705]
]

def psiTwoCell34Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell34Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell34Basis psiOneCell34Snapshot.corner psiTwoCell34Corner
      psiOneCell34Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell34Margin_checked

end Nuttall
