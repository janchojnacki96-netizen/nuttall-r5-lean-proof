import Nuttall.PsiCompactUniformPanel3Data
import Nuttall.PsiCompactUniformPanel4

namespace Nuttall

open W5

def psiOneCompactAnchor3 : QInterval := psiOneCompactAnchor4.add psiOneUniformPanel3

theorem psiOneCompactAnchor3_containsReal : psiOneCompactAnchor3.ContainsReal (psi 1 ((3/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor4.ContainsReal (psi 1 (((3+1:ℕ):ℝ)/32)) := by
    simpa [show (((3+1:ℕ):ℝ)/32) = ((4/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor4_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel3Jet j).ContainsReal (iteratedDeriv j Phi ((3:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel3Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 3) (by decide) hright hj psiOneUniformPanel3_checked
  simpa only [psiOneCompactAnchor3, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor3_containsReal

end Nuttall
