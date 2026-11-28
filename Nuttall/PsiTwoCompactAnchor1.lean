import Nuttall.PsiCompactUniformPanel1
import Nuttall.PsiTwoCompactAnchor2

namespace Nuttall

open W5

def psiTwoCompactAnchor1 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor2 psiTwoCompactAnchor2 psiOneUniformPanel1Jet (1/32)

theorem psiTwoCompactAnchor1_containsReal :
    psiTwoCompactAnchor1.ContainsReal (psi 2 ((1/32:ℚ):ℝ)) := by
  have hnext : ((1/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((2/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor2_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor2_containsReal)
    psiOneUniformPanel1Jet_containsReal

#print axioms psiTwoCompactAnchor1_containsReal

end Nuttall
