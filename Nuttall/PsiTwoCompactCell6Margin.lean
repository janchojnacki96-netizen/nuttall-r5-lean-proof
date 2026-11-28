import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiTwoCompactPointRow
import Nuttall.PsiCompactCell6Data

namespace Nuttall

open W5

def psiTwoCell6Corner : FixedIntInterval := ⟨3458140063036310748774583, 3458140063036516451868519⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[19374, 0, 0, 0, 0, 0, 0, 0],
  #v[35474, 39472, 0, 0, 0, 0, 0, 0],
  #v[46802, 87890, 56788, 0, 0, 0, 0, 0],
  #v[51859, 130528, 131705, 67378, 0, 0, 0, 0],
  #v[47324, 146350, 200121, 143712, 68861, 0, 0, 0],
  #v[35030, 123488, 198857, 200020, 109418, 57596, 0, 0],
  #v[37412, 139700, 243173, 248897, 195124, 73657, 42680, 0],
  #v[61897, 257603, 499219, 602718, 467035, 294694, 89580, 41031]
]

def psiTwoCell6Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell6Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell6Basis psiOneCell6Snapshot.corner psiTwoCell6Corner
      psiOneCell6Snapshot.jets j < psiTwoCompactThreshold := by
  rw [← psiTwoCompactPointRow_eq]
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell6Margin_checked

end Nuttall
