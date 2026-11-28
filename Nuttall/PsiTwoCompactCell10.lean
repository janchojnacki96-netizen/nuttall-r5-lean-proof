import Nuttall.PsiTwoCompactCell10Margin
import Nuttall.PsiCompactCell10Jets
import Nuttall.PsiTwoCompactAnchor3

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell10Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 3/32 - psiOneDyadicCenter 10
    let rawOne := psiOnePanelBox psiOneCompactAnchor3 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor3 psiTwoCompactAnchor3 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell10Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell10Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell10_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 10/128 ≤ t) (hU : t ≤ 11/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  have hanchor : ((3/32:ℚ):ℝ) = (((3:ℕ):ℝ)/32) := by norm_num
  refine psiTwo_compact_dyadic_snapshot_sound 10 3 (by decide) (by decide +kernel)
    psiOneCompactAnchor3 psiTwoCompactAnchor3 ?_ ?_ psiOneCell10Snapshot psiTwoCell10Corner
    psiOneCell10Inputs_checked psiOneCell10Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell10Basis ?_ ?_ ?_ psiTwoCell10Margin_checked p hp t ?_ ?_
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
  · change (((10:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((11:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiTwo_compact_cell10_signed_wronskians

end Nuttall
