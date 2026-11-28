import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell14Data

namespace Nuttall

open W5

def psiTwoCell14Corner : FixedIntInterval := ⟨1234757347532926739440222, 1234757347533124147102973⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[32423, 0, 0, 0, 0, 0, 0, 0],
  #v[68361, 58310, 0, 0, 0, 0, 0, 0],
  #v[103170, 155386, 74161, 0, 0, 0, 0, 0],
  #v[128164, 263799, 213515, 77107, 0, 0, 0, 0],
  #v[137099, 347989, 380687, 220421, 69147, 0, 0, 0],
  #v[133948, 394824, 523407, 404968, 186290, 55346, 0, 0],
  #v[128787, 428307, 656679, 603684, 372223, 141337, 42221, 0],
  #v[99601, 379565, 677545, 749136, 551482, 304521, 97529, 32697]
]

def psiTwoCell14Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell14Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell14Basis psiOneCell14Snapshot.corner psiTwoCell14Corner
      psiOneCell14Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell14Margin_checked

end Nuttall
