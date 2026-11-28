import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell43Data

namespace Nuttall

open W5

def psiTwoCell43Corner : FixedIntInterval := ⟨1058028620996272065505, 1058028621164075567576⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[1107646, 0, 0, 0, 0, 0, 0, 0],
  #v[3794453, 1266722, 0, 0, 0, 0, 0, 0],
  #v[9207847, 5880890, 1024359, 0, 0, 0, 0, 0],
  #v[18270820, 16804551, 5570977, 676366, 0, 0, 0, 0],
  #v[31435818, 37119436, 17650063, 4054140, 386762, 0, 0, 0],
  #v[48427975, 68995753, 41982979, 13770210, 2468282, 197813, 0, 0],
  #v[68167439, 112730163, 82543738, 34525816, 8794060, 1313656, 92358, 0],
  #v[88907021, 166225900, 140963694, 70750864, 22894927, 4833787, 627556, 39923]
]

def psiTwoCell43Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell43Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell43Basis psiOneCell43Snapshot.corner psiTwoCell43Corner
      psiOneCell43Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell43Margin_checked

end Nuttall
