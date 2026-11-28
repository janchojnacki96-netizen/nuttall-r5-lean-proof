import Nuttall.PsiTwoCompactCell12Margin
import Nuttall.PsiCompactCell12Jets
import Nuttall.PsiTwoCompactAnchor4

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell12Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 4/32 - psiOneDyadicCenter 12
    let rawOne := psiOnePanelBox psiOneCompactAnchor4 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor4 psiTwoCompactAnchor4 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell12Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell12Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell12_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 12/128 ≤ t) (hU : t ≤ 13/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  have hanchor : ((4/32:ℚ):ℝ) = (((4:ℕ):ℝ)/32) := by norm_num
  refine psiTwo_compact_dyadic_snapshot_sound 12 4 (by decide) (by decide +kernel)
    psiOneCompactAnchor4 psiTwoCompactAnchor4 ?_ ?_ psiOneCell12Snapshot psiTwoCell12Corner
    psiOneCell12Inputs_checked psiOneCell12Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell12Basis ?_ ?_ ?_ psiTwoCell12Margin_checked p hp t ?_ ?_
  · rw [← hanchor]
    exact psiOneCompactAnchor4_containsReal
  · rw [← hanchor]
    exact psiTwoCompactAnchor4_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (((12:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((13:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiTwo_compact_cell12_signed_wronskians

end Nuttall
