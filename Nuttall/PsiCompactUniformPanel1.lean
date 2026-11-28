import Nuttall.PsiCompactUniformPanel1Data
import Nuttall.PsiCompactUniformPanel2

namespace Nuttall

open W5

def psiOneCompactAnchor1 : QInterval := psiOneCompactAnchor2.add psiOneUniformPanel1

theorem psiOneCompactAnchor1_containsReal : psiOneCompactAnchor1.ContainsReal (psi 1 ((1/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor2.ContainsReal (psi 1 (((1+1:ℕ):ℝ)/32)) := by
    simpa [show (((1+1:ℕ):ℝ)/32) = ((2/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor2_containsReal
  have hnode : ((1/32:ℚ):ℝ) = (((1:ℕ):ℝ)/32) := by norm_num
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel1Jet j).ContainsReal (iteratedDeriv j Phi (((1:ℕ):ℝ)/32)) := by
    rw [← hnode]
    exact psiOneUniformPanel1Jet_containsReal j hj
  rw [hnode]
  exact psiOne_compact_panel_step (i := 1) (by decide) hright hj psiOneUniformPanel1_checked

#print axioms psiOneCompactAnchor1_containsReal

end Nuttall
