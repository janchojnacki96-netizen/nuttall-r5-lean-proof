import Nuttall.PsiCompactUniformPanel4
import Nuttall.PsiTwoCompactAnchor5

namespace Nuttall

open W5

def psiTwoCompactAnchor4 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor5 psiTwoCompactAnchor5 psiOneUniformPanel4Jet (1/32)

theorem psiTwoCompactAnchor4_containsReal :
    psiTwoCompactAnchor4.ContainsReal (psi 2 ((4/32:ℚ):ℝ)) := by
  have hnext : ((4/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((5/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor5_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor5_containsReal)
    psiOneUniformPanel4Jet_containsReal

#print axioms psiTwoCompactAnchor4_containsReal

end Nuttall
