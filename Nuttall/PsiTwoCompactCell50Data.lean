import Nuttall.PsiCompactCell50Data
import Nuttall.PsiTwoCompactCellSigns

namespace Nuttall

open W5

def psiTwoCell50Two : FixedIntInterval := ⟨56140028081870808196, 56140028242634388531⟩

private def psiTwoCell50BasisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[4808542, 0, 0, 0, 0, 0, 0, 0],
  #v[18452658, 4929488, 0, 0, 0, 0, 0, 0],
  #v[50128248, 25859317, 3573368, 0, 0, 0, 0, 0],
  #v[111297160, 83336555, 22165320, 2114999, 0, 0, 0, 0],
  #v[214182859, 207312513, 79821174, 14606734, 1084111, 0, 0, 0],
  #v[368941080, 433487612, 215269142, 56859415, 8060340, 497035, 0, 0],
  #v[580529930, 796025242, 478934087, 162764220, 33197822, 3892090, 208018, 0],
  #v[846222995, 1318256261, 924081998, 379711345, 99389950, 16707259, 1688968, 80605]
]

def psiTwoCell50Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j => (psiTwoCell50BasisRows.get i).get j

end Nuttall
