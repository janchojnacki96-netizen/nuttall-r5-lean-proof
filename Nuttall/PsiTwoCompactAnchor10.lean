import Nuttall.PsiCompactUniformPanel10
import Nuttall.PsiTwoCompactAnchor11

namespace Nuttall

open W5

def psiTwoCompactAnchor10 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor11 psiTwoCompactAnchor11 psiOneUniformPanel10Jet (1/32)

theorem psiTwoCompactAnchor10_containsReal :
    psiTwoCompactAnchor10.ContainsReal (psi 2 ((10/32:ℚ):ℝ)) := by
  have hnext : ((10/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((11/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor11_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor11_containsReal)
    psiOneUniformPanel10Jet_containsReal

#print axioms psiTwoCompactAnchor10_containsReal

end Nuttall
