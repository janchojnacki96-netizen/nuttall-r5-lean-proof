import Nuttall.PsiCompactUniformPanel5Data
import Nuttall.PsiCompactUniformPanel6

namespace Nuttall

open W5

def psiOneCompactAnchor5 : QInterval := psiOneCompactAnchor6.add psiOneUniformPanel5

theorem psiOneCompactAnchor5_containsReal : psiOneCompactAnchor5.ContainsReal (psi 1 ((5/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor6.ContainsReal (psi 1 (((5+1:ℕ):ℝ)/32)) := by
    simpa [show (((5+1:ℕ):ℝ)/32) = ((6/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor6_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel5Jet j).ContainsReal (iteratedDeriv j Phi ((5:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel5Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 5) (by decide) hright hj psiOneUniformPanel5_checked
  simpa only [psiOneCompactAnchor5, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor5_containsReal

end Nuttall
