import Nuttall.PsiCompactCell48
import Nuttall.PsiTwoCompactCell48Margin
import Nuttall.PsiTwoCompactAnchor13

namespace Nuttall

open W5
open scoped BigOperators

private def psiTwoCell48Raw : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor13 psiTwoCompactAnchor13 psiOneCell48PhiJet (7/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem psiTwoCell48Raw_checked :
    (psiTwoCell48Two.asQInterval (2^90)).lo ≤ psiTwoCell48Raw.lo ∧
    psiTwoCell48Raw.hi ≤ (psiTwoCell48Two.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiTwoCell48Corner_containsReal :
    (psiTwoCell48Two.asQInterval (2^90)).ContainsReal (psi 2 ((97/256:ℚ):ℝ)) := by
  have he : ((97/256:ℚ):ℝ)+((7/256:ℚ):ℝ) = ((13/32:ℚ):ℝ) := by norm_num
  have h : psiTwoCell48Raw.ContainsReal (psi 2 ((97/256:ℚ):ℝ)) :=
    psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
      (by rw [he]; exact psiOneCompactAnchor13_containsReal)
      (by rw [he]; exact psiTwoCompactAnchor13_containsReal)
      psiOneCell48PhiJet_containsReal
  exact compactContainsReal_of_endpoints psiTwoCell48Raw_checked.1 psiTwoCell48Raw_checked.2 h

theorem psiTwo_compact_cell48_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (hL : 3/8 ≤ t) (hU : t ≤ 49/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  let v := 256*t-97
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((97/256:ℚ):ℝ)+(1/256)*v = t := by dsimp [v]; push_cast; ring
  rw [← ht]
  apply psiTwo_compact_fixed_cell_signed_wronskians hp (by norm_num) (by norm_num) hv
    psiTwoCell48Basis ?_ ?_ ?_ psiOneCell48CornerFixed psiTwoCell48Two psiOneCell48PhiJetFixed ?_
    psiTwoCell48Corner_containsReal ?_ psiTwoCell48Margin_checked
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · exact psiOneCell48Corner_containsReal
  · exact psiOneCell48PhiJet_containsReal

#print axioms psiTwo_compact_cell48_signed_wronskians

end Nuttall
