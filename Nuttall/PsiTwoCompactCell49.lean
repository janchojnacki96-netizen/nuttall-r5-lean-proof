import Nuttall.PsiCompactCell49
import Nuttall.PsiTwoCompactCell49Margin
import Nuttall.PsiTwoCompactAnchor13

namespace Nuttall

open W5
open scoped BigOperators

private def psiTwoCell49Raw : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor13 psiTwoCompactAnchor13 psiOneCell49PhiJet (5/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem psiTwoCell49Raw_checked :
    (psiTwoCell49Two.asQInterval (2^90)).lo ≤ psiTwoCell49Raw.lo ∧
    psiTwoCell49Raw.hi ≤ (psiTwoCell49Two.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiTwoCell49Corner_containsReal :
    (psiTwoCell49Two.asQInterval (2^90)).ContainsReal (psi 2 ((99/256:ℚ):ℝ)) := by
  have he : ((99/256:ℚ):ℝ)+((5/256:ℚ):ℝ) = ((13/32:ℚ):ℝ) := by norm_num
  have h : psiTwoCell49Raw.ContainsReal (psi 2 ((99/256:ℚ):ℝ)) :=
    psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
      (by rw [he]; exact psiOneCompactAnchor13_containsReal)
      (by rw [he]; exact psiTwoCompactAnchor13_containsReal)
      psiOneCell49PhiJet_containsReal
  exact compactContainsReal_of_endpoints psiTwoCell49Raw_checked.1 psiTwoCell49Raw_checked.2 h

theorem psiTwo_compact_cell49_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (hL : 49/128 ≤ t) (hU : t ≤ 25/64) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  let v := 256*t-99
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((99/256:ℚ):ℝ)+(1/256)*v = t := by dsimp [v]; push_cast; ring
  rw [← ht]
  apply psiTwo_compact_fixed_cell_signed_wronskians hp (by norm_num) (by norm_num) hv
    psiTwoCell49Basis ?_ ?_ ?_ psiOneCell49CornerFixed psiTwoCell49Two psiOneCell49PhiJetFixed ?_
    psiTwoCell49Corner_containsReal ?_ psiTwoCell49Margin_checked
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · exact psiOneCell49Corner_containsReal
  · exact psiOneCell49PhiJet_containsReal

#print axioms psiTwo_compact_cell49_signed_wronskians

end Nuttall
