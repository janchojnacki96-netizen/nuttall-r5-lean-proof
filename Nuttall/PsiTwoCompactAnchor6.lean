import Nuttall.PsiCompactUniformPanel6
import Nuttall.PsiTwoCompactAnchor7

namespace Nuttall

open W5

def psiTwoCompactAnchor6 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor7 psiTwoCompactAnchor7 psiOneUniformPanel6Jet (1/32)

theorem psiTwoCompactAnchor6_containsReal :
    psiTwoCompactAnchor6.ContainsReal (psi 2 ((6/32:ℚ):ℝ)) := by
  have hnext : ((6/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((7/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor7_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor7_containsReal)
    psiOneUniformPanel6Jet_containsReal

#print axioms psiTwoCompactAnchor6_containsReal

end Nuttall
