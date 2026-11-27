import Nuttall.PsiCompactCell50
import Nuttall.PsiTwoCompactCell50Margin
import Nuttall.PsiTwoCompactAnchor13

namespace Nuttall

open W5
open scoped BigOperators

private def psiTwoCell50Raw : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor13 psiTwoCompactAnchor13 psiOneCell50PhiJet (3/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem psiTwoCell50Raw_checked :
    (psiTwoCell50Two.asQInterval (2^90)).lo ≤ psiTwoCell50Raw.lo ∧
    psiTwoCell50Raw.hi ≤ (psiTwoCell50Two.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiTwoCell50Corner_containsReal :
    (psiTwoCell50Two.asQInterval (2^90)).ContainsReal (psi 2 ((101/256:ℚ):ℝ)) := by
  have he : ((101/256:ℚ):ℝ)+((3/256:ℚ):ℝ) = ((13/32:ℚ):ℝ) := by norm_num
  have h : psiTwoCell50Raw.ContainsReal (psi 2 ((101/256:ℚ):ℝ)) :=
    psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
      (by rw [he]; exact psiOneCompactAnchor13_containsReal)
      (by rw [he]; exact psiTwoCompactAnchor13_containsReal)
      psiOneCell50PhiJet_containsReal
  exact compactContainsReal_of_endpoints psiTwoCell50Raw_checked.1 psiTwoCell50Raw_checked.2 h

theorem psiTwo_compact_cell50_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (hL : 25/64 ≤ t) (hU : t ≤ 51/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  let v := 256*t-101
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((101/256:ℚ):ℝ)+(1/256)*v = t := by dsimp [v]; push_cast; ring
  rw [← ht]
  apply psiTwo_compact_fixed_cell_signed_wronskians hp (by norm_num) (by norm_num) hv
    psiTwoCell50Basis ?_ ?_ ?_ psiOneCell50CornerFixed psiTwoCell50Two psiOneCell50PhiJetFixed ?_
    psiTwoCell50Corner_containsReal ?_ psiTwoCell50Margin_checked
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · exact psiOneCell50Corner_containsReal
  · exact psiOneCell50PhiJet_containsReal

#print axioms psiTwo_compact_cell50_signed_wronskians

end Nuttall
