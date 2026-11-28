import Nuttall.PsiTwoCompactCell24Margin
import Nuttall.PsiCompactCell24Jets
import Nuttall.PsiTwoCompactAnchor7

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell24Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 7/32 - psiOneDyadicCenter 24
    let rawOne := psiOnePanelBox psiOneCompactAnchor7 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor7 psiTwoCompactAnchor7 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell24Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell24Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell24_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 24/128 ≤ t) (hU : t ≤ 25/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 24 7 (by decide) (by decide +kernel)
    psiOneCompactAnchor7 psiTwoCompactAnchor7 ?_ ?_ psiOneCell24Snapshot psiTwoCell24Corner
    psiOneCell24Inputs_checked psiOneCell24Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell24Basis ?_ ?_ ?_ psiTwoCell24Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor7_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor7_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (24:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (25:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell24_signed_wronskians

end Nuttall
