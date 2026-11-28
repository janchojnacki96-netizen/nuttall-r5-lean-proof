import Nuttall.PsiCompactUniformPanel2Data
import Nuttall.PsiCompactUniformPanel3

namespace Nuttall

open W5

def psiOneCompactAnchor2 : QInterval := psiOneCompactAnchor3.add psiOneUniformPanel2

theorem psiOneCompactAnchor2_containsReal : psiOneCompactAnchor2.ContainsReal (psi 1 ((2/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor3.ContainsReal (psi 1 (((2+1:ℕ):ℝ)/32)) := by
    simpa [show (((2+1:ℕ):ℝ)/32) = ((3/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor3_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel2Jet j).ContainsReal (iteratedDeriv j Phi ((2:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel2Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 2) (by decide) hright hj psiOneUniformPanel2_checked
  simpa only [psiOneCompactAnchor2, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor2_containsReal

end Nuttall
