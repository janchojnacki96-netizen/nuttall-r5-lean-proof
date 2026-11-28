import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell35Data

namespace Nuttall

open W5

def psiTwoCell35Corner : FixedIntInterval := ⟨14872999934503239426358, 14872999934679137608791⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[295427, 0, 0, 0, 0, 0, 0, 0],
  #v[887744, 382823, 0, 0, 0, 0, 0, 0],
  #v[1891996, 1539259, 350788, 0, 0, 0, 0, 0],
  #v[3299943, 3823141, 1629089, 262455, 0, 0, 0, 0],
  #v[4993745, 7358438, 4437393, 1322427, 170059, 0, 0, 0],
  #v[6769511, 11939533, 9114303, 3817511, 896436, 98558, 0, 0],
  #v[8387827, 17052372, 15522972, 8188566, 2681990, 530015, 52143, 0],
  #v[9633739, 22006244, 23020877, 14424270, 5917298, 1617674, 280543, 25541]
]

def psiTwoCell35Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell35Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell35Basis psiOneCell35Snapshot.corner psiTwoCell35Corner
      psiOneCell35Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell35Margin_checked

end Nuttall
