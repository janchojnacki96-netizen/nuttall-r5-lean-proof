import Nuttall.PsiTwoCompactCell28Margin
import Nuttall.PsiCompactCell28Jets
import Nuttall.PsiTwoCompactAnchor8

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell28Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 8/32 - psiOneDyadicCenter 28
    let rawOne := psiOnePanelBox psiOneCompactAnchor8 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor8 psiTwoCompactAnchor8 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell28Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell28Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell28_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 28/128 ≤ t) (hU : t ≤ 29/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 28 8 (by decide) (by decide +kernel)
    psiOneCompactAnchor8 psiTwoCompactAnchor8 ?_ ?_ psiOneCell28Snapshot psiTwoCell28Corner
    psiOneCell28Inputs_checked psiOneCell28Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell28Basis ?_ ?_ ?_ psiTwoCell28Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor8_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor8_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (28:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (29:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell28_signed_wronskians

end Nuttall
