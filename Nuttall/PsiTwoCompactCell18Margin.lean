import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell18Data

namespace Nuttall

open W5

def psiTwoCell18Corner : FixedIntInterval := ⟨659935092646414674058068, 659935092646607954778341⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[44351, 0, 0, 0, 0, 0, 0, 0],
  #v[100191, 74937, 0, 0, 0, 0, 0, 0],
  #v[161557, 217098, 89545, 0, 0, 0, 0, 0],
  #v[213929, 396394, 285103, 87396, 0, 0, 0, 0],
  #v[245602, 564520, 553144, 283910, 73771, 0, 0, 0],
  #v[255262, 687094, 825679, 570236, 233869, 55810, 0, 0],
  #v[244207, 746511, 1047179, 877971, 482508, 167217, 38999, 0],
  #v[195702, 668378, 1068120, 1051660, 697389, 331644, 100170, 24685]
]

def psiTwoCell18Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell18Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell18Basis psiOneCell18Snapshot.corner psiTwoCell18Corner
      psiOneCell18Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell18Margin_checked

end Nuttall
