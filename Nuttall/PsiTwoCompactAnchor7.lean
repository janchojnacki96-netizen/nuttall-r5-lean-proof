import Nuttall.PsiCompactUniformPanel7
import Nuttall.PsiTwoCompactAnchor8

namespace Nuttall

open W5

def psiTwoCompactAnchor7 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor8 psiTwoCompactAnchor8 psiOneUniformPanel7Jet (1/32)

theorem psiTwoCompactAnchor7_containsReal :
    psiTwoCompactAnchor7.ContainsReal (psi 2 ((7/32:ℚ):ℝ)) := by
  have hnext : ((7/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((8/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor8_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor8_containsReal)
    psiOneUniformPanel7Jet_containsReal

#print axioms psiTwoCompactAnchor7_containsReal

end Nuttall
