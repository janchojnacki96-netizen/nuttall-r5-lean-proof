import Nuttall.PsiCompactUniformPanel9
import Nuttall.PsiTwoCompactAnchor10

namespace Nuttall

open W5

def psiTwoCompactAnchor9 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor10 psiTwoCompactAnchor10 psiOneUniformPanel9Jet (1/32)

theorem psiTwoCompactAnchor9_containsReal :
    psiTwoCompactAnchor9.ContainsReal (psi 2 ((9/32:ℚ):ℝ)) := by
  have hnext : ((9/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((10/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor10_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor10_containsReal)
    psiOneUniformPanel9Jet_containsReal

#print axioms psiTwoCompactAnchor9_containsReal

end Nuttall
