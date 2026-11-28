import Nuttall.PsiTwoCompactCell18Margin
import Nuttall.PsiCompactCell18Jets
import Nuttall.PsiTwoCompactAnchor5

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell18Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 5/32 - psiOneDyadicCenter 18
    let rawOne := psiOnePanelBox psiOneCompactAnchor5 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor5 psiTwoCompactAnchor5 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell18Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell18Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell18_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 18/128 ≤ t) (hU : t ≤ 19/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  have hanchor : ((5/32:ℚ):ℝ) = (((5:ℕ):ℝ)/32) := by norm_num
  refine psiTwo_compact_dyadic_snapshot_sound 18 5 (by decide) (by decide +kernel)
    psiOneCompactAnchor5 psiTwoCompactAnchor5 ?_ ?_ psiOneCell18Snapshot psiTwoCell18Corner
    psiOneCell18Inputs_checked psiOneCell18Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell18Basis ?_ ?_ ?_ psiTwoCell18Margin_checked p hp t ?_ ?_
  · rw [← hanchor]
    exact psiOneCompactAnchor5_containsReal
  · rw [← hanchor]
    exact psiTwoCompactAnchor5_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (((18:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((19:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiTwo_compact_cell18_signed_wronskians

end Nuttall
