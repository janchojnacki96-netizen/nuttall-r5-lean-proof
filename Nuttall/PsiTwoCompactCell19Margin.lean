import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiTwoCompactPointRow
import Nuttall.PsiCompactCell19Data

namespace Nuttall

open W5

def psiTwoCell19Corner : FixedIntInterval := ⟨556824134971192733391942, 556824134971384987044130⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[48283, 0, 0, 0, 0, 0, 0, 0],
  #v[110958, 80318, 0, 0, 0, 0, 0, 0],
  #v[181898, 237486, 94489, 0, 0, 0, 0, 0],
  #v[244786, 441642, 308259, 90784, 0, 0, 0, 0],
  #v[285809, 640673, 610613, 303881, 75467, 0, 0, 0],
  #v[301453, 792701, 928891, 623509, 248050, 56219, 0, 0],
  #v[291050, 869878, 1191507, 974143, 519747, 175186, 38511, 0],
  #v[241800, 805155, 1253022, 1199240, 773104, 354478, 104520, 23881]
]

def psiTwoCell19Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell19Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell19Basis psiOneCell19Snapshot.corner psiTwoCell19Corner
      psiOneCell19Snapshot.jets j < psiTwoCompactThreshold := by
  rw [← psiTwoCompactPointRow_eq]
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell19Margin_checked

end Nuttall
