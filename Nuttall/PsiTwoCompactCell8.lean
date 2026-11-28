import Nuttall.PsiTwoCompactCell8Margin
import Nuttall.PsiCompactCell8Jets
import Nuttall.PsiTwoCompactAnchor3

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell8Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 3/32 - psiOneDyadicCenter 8
    let rawOne := psiOnePanelBox psiOneCompactAnchor3 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor3 psiTwoCompactAnchor3 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell8Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell8Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell8_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 8/128 ≤ t) (hU : t ≤ 9/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  have hanchor : ((3/32:ℚ):ℝ) = (((3:ℕ):ℝ)/32) := by norm_num
  refine psiTwo_compact_dyadic_snapshot_sound 8 3 (by decide) (by decide +kernel)
    psiOneCompactAnchor3 psiTwoCompactAnchor3 ?_ ?_ psiOneCell8Snapshot psiTwoCell8Corner
    psiOneCell8Inputs_checked psiOneCell8Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell8Basis ?_ ?_ ?_ psiTwoCell8Margin_checked p hp t ?_ ?_
  · rw [← hanchor]
    exact psiOneCompactAnchor3_containsReal
  · rw [← hanchor]
    exact psiTwoCompactAnchor3_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (((8:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((9:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiTwo_compact_cell8_signed_wronskians

end Nuttall
