import Nuttall.PsiCompactUniformPanel13
import Nuttall.PsiTwoCompactRightAnchors

namespace Nuttall

open W5

/-- Weighted continuation through the existing Ψ₁ panel from 14/32 to 13/32. -/
def psiTwoCompactAnchor13 : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor14 psiTwoCompactAnchor14 psiOneUniformPanel13Jet (1/32)

theorem psiTwoCompactAnchor13_containsReal :
    psiTwoCompactAnchor13.ContainsReal (psi 2 ((13/32:ℚ):ℝ)) := by
  have hnext : ((13/32:ℚ):ℝ)+((1/32:ℚ):ℝ) = ((14/32:ℚ):ℝ) := by norm_num
  exact psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
    (by rw [hnext]; exact psiOneCompactAnchor14_containsReal)
    (by rw [hnext]; exact psiTwoCompactAnchor14_containsReal)
    psiOneUniformPanel13Jet_containsReal

#print axioms psiTwoCompactAnchor13_containsReal

end Nuttall
