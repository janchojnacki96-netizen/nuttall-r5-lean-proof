import Nuttall.PsiTwoCompactCell26Margin
import Nuttall.PsiCompactCell26Jets
import Nuttall.PsiTwoCompactAnchor7

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell26Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 7/32 - psiOneDyadicCenter 26
    let rawOne := psiOnePanelBox psiOneCompactAnchor7 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor7 psiTwoCompactAnchor7 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell26Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell26Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell26_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 26/128 ≤ t) (hU : t ≤ 27/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 26 7 (by decide) (by decide +kernel)
    psiOneCompactAnchor7 psiTwoCompactAnchor7 ?_ ?_ psiOneCell26Snapshot psiTwoCell26Corner
    psiOneCell26Inputs_checked psiOneCell26Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell26Basis ?_ ?_ ?_ psiTwoCell26Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor7_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor7_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (26:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (27:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell26_signed_wronskians

end Nuttall
