import Nuttall.PsiTwoCompactCell2Margin
import Nuttall.PsiCompactCell2Jets
import Nuttall.PsiTwoCompactAnchor1

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell2Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 1/32 - psiOneDyadicCenter 2
    let rawOne := psiOnePanelBox psiOneCompactAnchor1 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor1 psiTwoCompactAnchor1 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell2Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell2Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell2_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 2/128 ≤ t) (hU : t ≤ 3/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  have hanchor : ((1/32:ℚ):ℝ) = (((1:ℕ):ℝ)/32) := by norm_num
  refine psiTwo_compact_dyadic_snapshot_sound 2 1 (by decide) (by decide +kernel)
    psiOneCompactAnchor1 psiTwoCompactAnchor1 ?_ ?_ psiOneCell2Snapshot psiTwoCell2Corner
    psiOneCell2Inputs_checked psiOneCell2Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell2Basis ?_ ?_ ?_ psiTwoCell2Margin_checked p hp t ?_ ?_
  · rw [← hanchor]
    exact psiOneCompactAnchor1_containsReal
  · rw [← hanchor]
    exact psiTwoCompactAnchor1_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (((2:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((3:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiTwo_compact_cell2_signed_wronskians

end Nuttall
