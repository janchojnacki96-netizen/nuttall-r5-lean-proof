import Nuttall.PsiCompactUniformPanel9Data
import Nuttall.PsiCompactUniformPanel10

namespace Nuttall

open W5

def psiOneCompactAnchor9 : QInterval := psiOneCompactAnchor10.add psiOneUniformPanel9

theorem psiOneCompactAnchor9_containsReal : psiOneCompactAnchor9.ContainsReal (psi 1 ((9/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor10.ContainsReal (psi 1 (((9+1:ℕ):ℝ)/32)) := by
    simpa [show (((9+1:ℕ):ℝ)/32) = ((10/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor10_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel9Jet j).ContainsReal (iteratedDeriv j Phi ((9:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel9Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 9) (by decide) hright hj psiOneUniformPanel9_checked
  simpa only [psiOneCompactAnchor9, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor9_containsReal

end Nuttall
