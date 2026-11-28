import Nuttall.PsiTwoCompactCell3Margin
import Nuttall.PsiCompactCell3Jets
import Nuttall.PsiTwoCompactAnchor1

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell3Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 1/32 - psiOneDyadicCenter 3
    let rawOne := psiOnePanelBox psiOneCompactAnchor1 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor1 psiTwoCompactAnchor1 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell3Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell3Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell3_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 3/128 ≤ t) (hU : t ≤ 4/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  have hanchor : ((1/32:ℚ):ℝ) = (((1:ℕ):ℝ)/32) := by norm_num
  refine psiTwo_compact_dyadic_snapshot_sound 3 1 (by decide) (by decide +kernel)
    psiOneCompactAnchor1 psiTwoCompactAnchor1 ?_ ?_ psiOneCell3Snapshot psiTwoCell3Corner
    psiOneCell3Inputs_checked psiOneCell3Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell3Basis ?_ ?_ ?_ psiTwoCell3Margin_checked p hp t ?_ ?_
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
  · change (((3:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((4:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiTwo_compact_cell3_signed_wronskians

end Nuttall
