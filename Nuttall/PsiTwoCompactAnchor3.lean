import Nuttall.PsiCompactUniformPanel3
import Nuttall.PsiTwoCompactAnchor4

namespace Nuttall

open W5

def psiTwoCompactAnchor3 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor4 psiTwoCompactAnchor4 psiOneUniformPanel3Jet (1/32)

theorem psiTwoCompactAnchor3_containsReal :
    psiTwoCompactAnchor3.ContainsReal (psi 2 ((3/32:ℚ):ℝ)) := by
  have hnext : ((3/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((4/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor4_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor4_containsReal)
    psiOneUniformPanel3Jet_containsReal

#print axioms psiTwoCompactAnchor3_containsReal

end Nuttall
