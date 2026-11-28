import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell31Data

namespace Nuttall

open W5

def psiTwoCell31Corner : FixedIntInterval := ⟨44149522734896884620304, 44149522735076850905525⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[171469, 0, 0, 0, 0, 0, 0, 0],
  #v[482265, 236517, 0, 0, 0, 0, 0, 0],
  #v[962887, 883163, 230699, 0, 0, 0, 0, 0],
  #v[1574203, 2042684, 986197, 183736, 0, 0, 0, 0],
  #v[2233817, 3667177, 2485727, 843613, 126730, 0, 0, 0],
  #v[2840442, 5556724, 4738464, 2238841, 601723, 78185, 0, 0],
  #v[3301376, 7416485, 7504055, 4433456, 1643878, 373601, 44029, 0],
  #v[3559033, 8953485, 10366173, 7233310, 3331414, 1034669, 207191, 22957]
]

def psiTwoCell31Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell31Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell31Basis psiOneCell31Snapshot.corner psiTwoCell31Corner
      psiOneCell31Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell31Margin_checked

end Nuttall
