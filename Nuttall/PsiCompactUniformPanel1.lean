import Nuttall.PsiCompactUniformPanel1Data
import Nuttall.PsiCompactUniformPanel2

namespace Nuttall

open W5

def psiOneCompactAnchor1 : QInterval := psiOneCompactAnchor2.add psiOneUniformPanel1

theorem psiOneCompactAnchor1_containsReal : psiOneCompactAnchor1.ContainsReal (psi 1 ((1/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor2.ContainsReal (psi 1 (((1+1:ℕ):ℝ)/32)) := by
    simpa [show (((1+1:ℕ):ℝ)/32) = ((2/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor2_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel1Jet j).ContainsReal (iteratedDeriv j Phi ((1:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel1Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 1) (by decide) hright hj psiOneUniformPanel1_checked
  simpa only [psiOneCompactAnchor1, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor1_containsReal

end Nuttall
