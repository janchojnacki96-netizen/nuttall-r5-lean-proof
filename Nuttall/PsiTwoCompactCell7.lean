import Nuttall.PsiTwoCompactCell7Margin
import Nuttall.PsiCompactCell7Jets
import Nuttall.PsiTwoCompactAnchor2

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell7Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 2/32 - psiOneDyadicCenter 7
    let rawOne := psiOnePanelBox psiOneCompactAnchor2 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor2 psiTwoCompactAnchor2 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell7Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell7Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell7_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 7/128 ≤ t) (hU : t ≤ 8/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  have hanchor : ((2/32:ℚ):ℝ) = (((2:ℕ):ℝ)/32) := by norm_num
  refine psiTwo_compact_dyadic_snapshot_sound 7 2 (by decide) (by decide +kernel)
    psiOneCompactAnchor2 psiTwoCompactAnchor2 ?_ ?_ psiOneCell7Snapshot psiTwoCell7Corner
    psiOneCell7Inputs_checked psiOneCell7Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell7Basis ?_ ?_ ?_ psiTwoCell7Margin_checked p hp t ?_ ?_
  · rw [← hanchor]
    exact psiOneCompactAnchor2_containsReal
  · rw [← hanchor]
    exact psiTwoCompactAnchor2_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (((7:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((8:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiTwo_compact_cell7_signed_wronskians

end Nuttall
