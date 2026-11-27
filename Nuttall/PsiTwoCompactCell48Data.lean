import Nuttall.PsiCompactCell48Data
import Nuttall.PsiTwoCompactCellSigns

namespace Nuttall

open W5

def psiTwoCell48Two : FixedIntInterval := ⟨139011126273623323282, 139011126436385749591⟩

private def psiTwoCell48BasisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[3055800, 0, 0, 0, 0, 0, 0, 0],
  #v[11353410, 3232086, 0, 0, 0, 0, 0, 0],
  #v[29865774, 16378316, 2417292, 0, 0, 0, 0, 0],
  #v[64217269, 51009894, 14449012, 1476156, 0, 0, 0, 0],
  #v[119693779, 122677203, 50181942, 9798249, 780670, 0, 0, 0],
  #v[199708479, 248059467, 130600108, 36703942, 5562719, 369275, 0, 0],
  #v[304402306, 440605815, 280534517, 101202539, 21997100, 2762849, 159456, 0],
  #v[429844387, 705904556, 522801628, 227570314, 63309770, 11359141, 1232847, 63747]
]

def psiTwoCell48Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j => (psiTwoCell48BasisRows.get i).get j

end Nuttall
