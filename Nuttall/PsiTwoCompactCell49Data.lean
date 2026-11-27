import Nuttall.PsiCompactCell49Data
import Nuttall.PsiTwoCompactCellSigns

namespace Nuttall

open W5

def psiTwoCell49Two : FixedIntInterval := ⟨88979612498543877115, 88979612660306837545⟩

private def psiTwoCell49BasisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[3819482, 0, 0, 0, 0, 0, 0, 0],
  #v[14422208, 3977202, 0, 0, 0, 0, 0, 0],
  #v[38554045, 20506451, 2928457, 0, 0, 0, 0, 0],
  #v[84238711, 64968233, 17832528, 1760584, 0, 0, 0, 0],
  #v[159541397, 158912238, 63067402, 11921163, 916656, 0, 0, 0],
  #v[270472404, 326763661, 167088261, 45524743, 6672684, 426878, 0, 0],
  #v[418874154, 590147023, 365277760, 127903296, 26930727, 3267876, 181471, 0],
  #v[600959717, 961273523, 692662680, 292956017, 79056465, 13729586, 1438059, 71424]
]

def psiTwoCell49Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j => (psiTwoCell49BasisRows.get i).get j

end Nuttall
