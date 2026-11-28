import Nuttall.PsiCompactUniformPanel10Data
import Nuttall.PsiCompactUniformPanel11

namespace Nuttall

open W5

def psiOneCompactAnchor10 : QInterval := psiOneCompactAnchor11.add psiOneUniformPanel10

theorem psiOneCompactAnchor10_containsReal : psiOneCompactAnchor10.ContainsReal (psi 1 ((10/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor11.ContainsReal (psi 1 (((10+1:ℕ):ℝ)/32)) := by
    simpa [show (((10+1:ℕ):ℝ)/32) = ((11/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor11_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel10Jet j).ContainsReal (iteratedDeriv j Phi ((10:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel10Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 10) (by decide) hright hj psiOneUniformPanel10_checked
  simpa only [psiOneCompactAnchor10, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor10_containsReal

end Nuttall
