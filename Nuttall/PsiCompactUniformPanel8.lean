import Nuttall.PsiCompactUniformPanel8Data
import Nuttall.PsiCompactUniformPanel9

namespace Nuttall

open W5

def psiOneCompactAnchor8 : QInterval := psiOneCompactAnchor9.add psiOneUniformPanel8

theorem psiOneCompactAnchor8_containsReal : psiOneCompactAnchor8.ContainsReal (psi 1 ((8/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor9.ContainsReal (psi 1 (((8+1:ℕ):ℝ)/32)) := by
    simpa [show (((8+1:ℕ):ℝ)/32) = ((9/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor9_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel8Jet j).ContainsReal (iteratedDeriv j Phi ((8:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel8Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 8) (by decide) hright hj psiOneUniformPanel8_checked
  simpa only [psiOneCompactAnchor8, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor8_containsReal

end Nuttall
