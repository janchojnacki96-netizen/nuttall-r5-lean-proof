import Nuttall.PsiTwoCompactCell36Margin
import Nuttall.PsiCompactCell36Jets
import Nuttall.PsiTwoCompactAnchor10

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell36Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 10/32 - psiOneDyadicCenter 36
    let rawOne := psiOnePanelBox psiOneCompactAnchor10 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor10 psiTwoCompactAnchor10 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell36Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell36Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell36_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 36/128 ≤ t) (hU : t ≤ 37/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 36 10 (by decide) (by decide +kernel)
    psiOneCompactAnchor10 psiTwoCompactAnchor10 ?_ ?_ psiOneCell36Snapshot psiTwoCell36Corner
    psiOneCell36Inputs_checked psiOneCell36Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell36Basis ?_ ?_ ?_ psiTwoCell36Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor10_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor10_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (36:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (37:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell36_signed_wronskians

end Nuttall
