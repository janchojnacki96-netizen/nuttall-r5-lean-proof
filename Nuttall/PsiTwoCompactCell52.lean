import Nuttall.PsiCompactCell52
import Nuttall.PsiTwoCompactCell52Margin
import Nuttall.PsiTwoCompactRightAnchors

namespace Nuttall

open W5
open scoped BigOperators

private def psiTwoCell52Raw : QInterval :=
  psiTwoPanelBox psiOneCompactAnchor14 psiTwoCompactAnchor14 psiOneCell52PhiJet (7/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem psiTwoCell52Raw_checked :
    (psiTwoCell52Two.asQInterval (2^90)).lo ≤ psiTwoCell52Raw.lo ∧
    psiTwoCell52Raw.hi ≤ (psiTwoCell52Two.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiTwoCell52Corner_containsReal :
    (psiTwoCell52Two.asQInterval (2^90)).ContainsReal (psi 2 ((105/256:ℚ):ℝ)) := by
  have he : ((105/256:ℚ):ℝ)+((7/256:ℚ):ℝ) = ((14/32:ℚ):ℝ) := by norm_num
  have h : psiTwoCell52Raw.ContainsReal (psi 2 ((105/256:ℚ):ℝ)) :=
    psiTwoPanelBox_containsReal (by norm_num) (by norm_num) (by norm_num)
      (by rw [he]; exact psiOneCompactAnchor14_containsReal)
      (by rw [he]; exact psiTwoCompactAnchor14_containsReal)
      psiOneCell52PhiJet_containsReal
  exact compactContainsReal_of_endpoints psiTwoCell52Raw_checked.1 psiTwoCell52Raw_checked.2 h

theorem psiTwo_compact_cell52_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (hL : 13/32 ≤ t) (hU : t ≤ 53/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  let v := 256*t-105
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((105/256:ℚ):ℝ)+(1/256)*v = t := by dsimp [v]; push_cast; ring
  rw [← ht]
  apply psiTwo_compact_fixed_cell_signed_wronskians hp (by norm_num) (by norm_num) hv
    psiTwoCell52Basis ?_ ?_ ?_ psiTwoCell52One psiTwoCell52Two psiTwoCell52Phi ?_
    psiTwoCell52Corner_containsReal ?_ psiTwoCell52Margin_checked
  · exact (by
      decide +kernel : ∀ i j : Fin 8, i < j → psiTwoCell52Basis i j = 0)
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · rw [psiTwoCell52One_eq]
    exact psiOneCell52Corner_containsReal
  · intro j hj
    rw [psiTwoCell52Phi_eq j hj]
    exact psiOneCell52PhiJet_containsReal j hj

#print axioms psiTwo_compact_cell52_signed_wronskians

end Nuttall
