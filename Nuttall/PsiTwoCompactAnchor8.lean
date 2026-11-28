import Nuttall.PsiCompactUniformPanel8
import Nuttall.PsiTwoCompactAnchor9

namespace Nuttall

open W5

def psiTwoCompactAnchor8 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor9 psiTwoCompactAnchor9 psiOneUniformPanel8Jet (1/32)

theorem psiTwoCompactAnchor8_containsReal :
    psiTwoCompactAnchor8.ContainsReal (psi 2 ((8/32:ℚ):ℝ)) := by
  have hnext : ((8/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((9/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor9_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor9_containsReal)
    psiOneUniformPanel8Jet_containsReal

#print axioms psiTwoCompactAnchor8_containsReal

end Nuttall
