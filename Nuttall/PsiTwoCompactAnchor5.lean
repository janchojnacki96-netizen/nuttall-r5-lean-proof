import Nuttall.PsiCompactUniformPanel5
import Nuttall.PsiTwoCompactAnchor6

namespace Nuttall

open W5

def psiTwoCompactAnchor5 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor6 psiTwoCompactAnchor6 psiOneUniformPanel5Jet (1/32)

theorem psiTwoCompactAnchor5_containsReal :
    psiTwoCompactAnchor5.ContainsReal (psi 2 ((5/32:ℚ):ℝ)) := by
  have hnext : ((5/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((6/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor6_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor6_containsReal)
    psiOneUniformPanel5Jet_containsReal

#print axioms psiTwoCompactAnchor5_containsReal

end Nuttall
