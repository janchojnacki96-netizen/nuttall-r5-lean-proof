import Nuttall.PsiCompactUniformPanel2
import Nuttall.PsiTwoCompactAnchor3

namespace Nuttall

open W5

def psiTwoCompactAnchor2 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor3 psiTwoCompactAnchor3 psiOneUniformPanel2Jet (1/32)

theorem psiTwoCompactAnchor2_containsReal :
    psiTwoCompactAnchor2.ContainsReal (psi 2 ((2/32:ℚ):ℝ)) := by
  have hnext : ((2/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((3/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor3_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor3_containsReal)
    psiOneUniformPanel2Jet_containsReal

#print axioms psiTwoCompactAnchor2_containsReal

end Nuttall
