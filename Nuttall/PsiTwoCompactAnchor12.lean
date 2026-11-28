import Nuttall.PsiCompactUniformPanel12
import Nuttall.PsiTwoCompactAnchor13

namespace Nuttall

open W5

def psiTwoCompactAnchor12 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor13 psiTwoCompactAnchor13 psiOneUniformPanel12Jet (1/32)

theorem psiTwoCompactAnchor12_containsReal :
    psiTwoCompactAnchor12.ContainsReal (psi 2 ((12/32:ℚ):ℝ)) := by
  have hnext : ((12/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((13/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor13_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor13_containsReal)
    psiOneUniformPanel12Jet_containsReal

#print axioms psiTwoCompactAnchor12_containsReal

end Nuttall
