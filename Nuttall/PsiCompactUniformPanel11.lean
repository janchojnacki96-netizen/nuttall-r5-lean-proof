import Nuttall.PsiCompactUniformPanel11Data
import Nuttall.PsiCompactUniformPanel12

namespace Nuttall

open W5

def psiOneCompactAnchor11 : QInterval := psiOneCompactAnchor12.add psiOneUniformPanel11

theorem psiOneCompactAnchor11_containsReal : psiOneCompactAnchor11.ContainsReal (psi 1 ((11/32:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor12.ContainsReal (psi 1 (((11+1:ℕ):ℝ)/32)) := by
    simpa [show (((11+1:ℕ):ℝ)/32) = ((12/32:ℚ):ℝ) by norm_num] using
      psiOneCompactAnchor12_containsReal
  have hj (j : ℕ) (hj : j < 36) :
      (psiOneUniformPanel11Jet j).ContainsReal (iteratedDeriv j Phi ((11:ℝ)/32)) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using psiOneUniformPanel11Jet_containsReal j hj
  have h := psiOne_compact_panel_step (i := 11) (by decide) hright hj psiOneUniformPanel11_checked
  simpa only [psiOneCompactAnchor11, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using h

#print axioms psiOneCompactAnchor11_containsReal

end Nuttall
