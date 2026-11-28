import Nuttall.PsiCompactUniformPanel11
import Nuttall.PsiTwoCompactAnchor12

namespace Nuttall

open W5

def psiTwoCompactAnchor11 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor12 psiTwoCompactAnchor12 psiOneUniformPanel11Jet (1/32)

theorem psiTwoCompactAnchor11_containsReal :
    psiTwoCompactAnchor11.ContainsReal (psi 2 ((11/32:ℚ):ℝ)) := by
  have hnext : ((11/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((12/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor12_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor12_containsReal)
    psiOneUniformPanel11Jet_containsReal

#print axioms psiTwoCompactAnchor11_containsReal

end Nuttall
