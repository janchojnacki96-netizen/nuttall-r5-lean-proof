import Nuttall.PsiTwoCompactCell11Margin
import Nuttall.PsiCompactCell11Jets
import Nuttall.PsiTwoCompactAnchor3

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell11Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 3/32 - psiOneDyadicCenter 11
    let rawOne := psiOnePanelBox psiOneCompactAnchor3 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor3 psiTwoCompactAnchor3 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell11Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell11Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell11_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 11/128 ≤ t) (hU : t ≤ 12/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  have hanchor : ((3/32:ℚ):ℝ) = (((3:ℕ):ℝ)/32) := by norm_num
  refine psiTwo_compact_dyadic_snapshot_sound 11 3 (by decide) (by decide +kernel)
    psiOneCompactAnchor3 psiTwoCompactAnchor3 ?_ ?_ psiOneCell11Snapshot psiTwoCell11Corner
    psiOneCell11Inputs_checked psiOneCell11Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell11Basis ?_ ?_ ?_ psiTwoCell11Margin_checked p hp t ?_ ?_
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
  · change (((11:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((12:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiTwo_compact_cell11_signed_wronskians

end Nuttall
