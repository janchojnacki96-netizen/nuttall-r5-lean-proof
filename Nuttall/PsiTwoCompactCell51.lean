import Nuttall.PsiCompactCell51
import Nuttall.PsiTwoCompactCell51Margin
import Nuttall.PsiTwoCompactAnchor13

namespace Nuttall

open W5
open scoped BigOperators

private def psiTwoCell51Raw : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor13 psiTwoCompactAnchor13 psiOneCell51PhiJet (1/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem psiTwoCell51Raw_checked :
    (psiTwoCell51Two.asQInterval (2^90)).lo ≤ psiTwoCell51Raw.lo ∧
    psiTwoCell51Raw.hi ≤ (psiTwoCell51Two.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiTwoCell51Corner_containsReal :
    (psiTwoCell51Two.asQInterval (2^90)).ContainsReal (psi 2 ((103/256:ℚ):ℝ)) := by
  have he : ((103/256:ℚ):ℝ)+((1/256:ℚ):ℝ) = ((13/32:ℚ):ℝ) := by norm_num
  have h : psiTwoCell51Raw.ContainsReal (psi 2 ((103/256:ℚ):ℝ)) :=
    psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
      (by rw [he]; exact psiOneCompactAnchor13_containsReal)
      (by rw [he]; exact psiTwoCompactAnchor13_containsReal)
      psiOneCell51PhiJet_containsReal
  exact compactContainsReal_of_endpoints psiTwoCell51Raw_checked.1 psiTwoCell51Raw_checked.2 h

theorem psiTwo_compact_cell51_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (hL : 51/128 ≤ t) (hU : t ≤ 13/32) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  let v := 256*t-103
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((103/256:ℚ):ℝ)+(1/256)*v = t := by dsimp [v]; push_cast; ring
  rw [← ht]
  apply psiTwo_compact_fixed_cell_signed_wronskians hp (by norm_num) (by norm_num) hv
    psiTwoCell51Basis ?_ ?_ ?_ psiOneCell51CornerFixed psiTwoCell51Two psiOneCell51PhiJetFixed ?_
    psiTwoCell51Corner_containsReal ?_ psiTwoCell51Margin_checked
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · exact psiOneCell51Corner_containsReal
  · exact psiOneCell51PhiJet_containsReal

#print axioms psiTwo_compact_cell51_signed_wronskians

end Nuttall
