import Nuttall.PsiTwoCompactDyadicReplay
import Nuttall.PsiCompactCell28Data

namespace Nuttall

open W5

def psiTwoCell28Corner : FixedIntInterval := ⟨91504513853825966888698, 91504513854008983314539⟩

private def basisRows : Vector (Vector ℤ 8) 8 := #v[
  #v[119105, 0, 0, 0, 0, 0, 0, 0],
  #v[318658, 172166, 0, 0, 0, 0, 0, 0],
  #v[605746, 607499, 175987, 0, 0, 0, 0, 0],
  #v[943329, 1331275, 705518, 146887, 0, 0, 0, 0],
  #v[1275471, 2267653, 1676275, 626888, 106174, 0, 0, 0],
  #v[1545986, 3263925, 3020150, 1560366, 463791, 68651, 0, 0],
  #v[1712031, 4138754, 4526380, 2907384, 1182057, 298014, 40510, 0],
  #v[1759211, 4749605, 5923584, 4473674, 2243699, 766218, 170514, 22122]
]

def psiTwoCell28Basis : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a j => (basisRows.get a).get j

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiTwoCell28Margin_checked (j : Fin 8) :
    psiTwoCompactRow psiTwoCell28Basis psiOneCell28Snapshot.corner psiTwoCell28Corner
      psiOneCell28Snapshot.jets j < psiTwoCompactThreshold := by
  fin_cases j <;> decide +kernel

#print axioms psiTwoCell28Margin_checked

end Nuttall
