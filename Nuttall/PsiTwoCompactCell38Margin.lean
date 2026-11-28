import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell38Data

namespace Nuttall

open W5

def psiTwoCell38Corner : FixedIntInterval := ⟨5969912714183562053885, 5969912714356415739152⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[466300, 0, 0, 0, 0, 0, 0, 0],
  #v[1472063, 576587, 0, 0, 0, 0, 0, 0],
  #v[3294179, 2448257, 504149, 0, 0, 0, 0, 0],
  #v[6030710, 6411363, 2486884, 359926, 0, 0, 0, 0],
  #v[9576632, 12997136, 7173344, 1938895, 222537, 0, 0, 0],
  #v[13620197, 22194835, 15573725, 5954371, 1263394, 123067, 0, 0],
  #v[17703476, 33343457, 27999565, 13549697, 4040345, 718773, 62128, 0],
  #v[21325440, 45238117, 43787259, 25269994, 9491751, 2356209, 366533, 29038]
]

def psiTwoCell38Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell38Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell38Basis psiOneCell38Snapshot.corner psiTwoCell38Corner
      psiOneCell38Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell38Margin_checked

end Nuttall
