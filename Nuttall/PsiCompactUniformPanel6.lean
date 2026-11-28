import Nuttall.PsiCompactUniformPanel6Data
import Nuttall.PsiCompactUniformPanel7

namespace Nuttall

open W5

def psiOneCompactAnchor6 : QInterval := psiOneCompactAnchor7.add psiOneUniformPanel6

theorem psiOneCompactAnchor6_containsReal : psiOneCompactAnchor6.ContainsReal (psi 1 ((6/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor7.ContainsReal (psi 1 (((6+1:ℕ):ℝ)/32)) := by
    simpa [show (((6+1:ℕ):ℝ)/32) = ((7/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor7_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel6Jet j).ContainsReal (iteratedDeriv j Phi ((6:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel6Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 6) (by decide) hright hj psiOneUniformPanel6_checked
  simpa only [psiOneCompactAnchor6, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor6_containsReal

end Nuttall
