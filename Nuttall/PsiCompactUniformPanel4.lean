import Nuttall.PsiCompactUniformPanel4Data
import Nuttall.PsiCompactUniformPanel5

namespace Nuttall

open W5

def psiOneCompactAnchor4 : QInterval := psiOneCompactAnchor5.add psiOneUniformPanel4

theorem psiOneCompactAnchor4_containsReal : psiOneCompactAnchor4.ContainsReal (psi 1 ((4/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor5.ContainsReal (psi 1 (((4+1:ℕ):ℝ)/32)) := by
    simpa [show (((4+1:ℕ):ℝ)/32) = ((5/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor5_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel4Jet j).ContainsReal (iteratedDeriv j Phi ((4:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel4Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 4) (by decide) hright hj psiOneUniformPanel4_checked
  simpa only [psiOneCompactAnchor4, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor4_containsReal

end Nuttall
