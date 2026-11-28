import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell42Data

namespace Nuttall

open W5

def psiTwoCell42Corner : FixedIntInterval := ⟨1529486182465610350450, 1529486182634420155683⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[921249, 0, 0, 0, 0, 0, 0, 0],
  #v[3104900, 1070142, 0, 0, 0, 0, 0, 0],
  #v[7413636, 4881047, 879016, 0, 0, 0, 0, 0],
  #v[14475831, 13707531, 4689389, 589537, 0, 0, 0, 0],
  #v[24510444, 29764999, 14583168, 3460458, 342420, 0, 0, 0],
  #v[37160892, 54398000, 34063942, 11521924, 2136016, 177891, 0, 0],
  #v[51481160, 87402344, 65791297, 28338266, 7449873, 1152336, 84365, 0],
  #v[66085169, 126752901, 110399960, 56993221, 19004607, 4144844, 557873, 37042]
]

def psiTwoCell42Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell42Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell42Basis psiOneCell42Snapshot.corner psiTwoCell42Corner
      psiOneCell42Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell42Margin_checked

end Nuttall
