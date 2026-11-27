import Nuttall.PsiCompactCell51Data
import Nuttall.PsiTwoCompactCellSigns

namespace Nuttall

open W5

def psiTwoCell51Two : FixedIntInterval := ⟨34897736685943037056, 34897736845707238386⟩

private def psiTwoCell51BasisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[6098895, 0, 0, 0, 0, 0, 0, 0],
  #v[23785237, 6155375, 0, 0, 0, 0, 0, 0],
  #v[65661555, 32851029, 4392839, 0, 0, 0, 0, 0],
  #v[148138748, 107685795, 27753791, 2559720, 0, 0, 0, 0],
  #v[289671116, 272438821, 101762663, 18028255, 1291725, 0, 0, 0],
  #v[506988985, 579275987, 279352839, 71528715, 9807289, 583041, 0, 0],
  #v[810532304, 1081559160, 632477632, 208605404, 41214836, 4668884, 240228, 0],
  #v[1200411343, 1820983939, 1241669292, 495648078, 125832267, 20473706, 1997799, 91645]
]

def psiTwoCell51Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j => (psiTwoCell51BasisRows.get i).get j

end Nuttall
