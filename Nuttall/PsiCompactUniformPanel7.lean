import Nuttall.PsiCompactUniformPanel7Data
import Nuttall.PsiCompactUniformPanel8

namespace Nuttall

open W5

def psiOneCompactAnchor7 : QInterval := psiOneCompactAnchor8.add psiOneUniformPanel7

theorem psiOneCompactAnchor7_containsReal : psiOneCompactAnchor7.ContainsReal (psi 1 ((7/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor8.ContainsReal (psi 1 (((7+1:ℕ):ℝ)/32)) := by
    simpa [show (((7+1:ℕ):ℝ)/32) = ((8/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor8_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel7Jet j).ContainsReal (iteratedDeriv j Phi ((7:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel7Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 7) (by decide) hright hj psiOneUniformPanel7_checked
  simpa only [psiOneCompactAnchor7, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor7_containsReal

end Nuttall
