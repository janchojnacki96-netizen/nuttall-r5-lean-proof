import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell29Data

namespace Nuttall

open W5

def psiTwoCell29Corner : FixedIntInterval := ⟨72330815285626343388134, 72330815285808343043354⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[133964, 0, 0, 0, 0, 0, 0, 0],
  #v[364447, 190645, 0, 0, 0, 0, 0, 0],
  #v[704229, 685594, 191856, 0, 0, 0, 0, 0],
  #v[1114621, 1529759, 785949, 157650, 0, 0, 0, 0],
  #v[1531551, 2651880, 1904662, 689661, 112188, 0, 0, 0],
  #v[1886215, 3882903, 3496890, 1753831, 504137, 71413, 0, 0],
  #v[2122869, 5008717, 5338375, 3335183, 1315098, 320338, 41489, 0],
  #v[2216921, 5847031, 7114851, 5234289, 2552060, 844431, 181483, 22313]
]

def psiTwoCell29Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell29Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell29Basis psiOneCell29Snapshot.corner psiTwoCell29Corner
      psiOneCell29Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell29Margin_checked

end Nuttall
