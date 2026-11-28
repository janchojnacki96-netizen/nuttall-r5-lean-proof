import Nuttall.PsiTwoCompactCell21Margin
import Nuttall.PsiCompactCell21Jets
import Nuttall.PsiTwoCompactAnchor6

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell21Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 6/32 - psiOneDyadicCenter 21
    let rawOne := psiOnePanelBox psiOneCompactAnchor6 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor6 psiTwoCompactAnchor6 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell21Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell21Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell21_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 21/128 ≤ t) (hU : t ≤ 22/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 21 6 (by decide) (by decide +kernel)
    psiOneCompactAnchor6 psiTwoCompactAnchor6 ?_ ?_ psiOneCell21Snapshot psiTwoCell21Corner
    psiOneCell21Inputs_checked psiOneCell21Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell21Basis ?_ ?_ ?_ psiTwoCell21Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor6_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor6_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (21:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (22:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell21_signed_wronskians

end Nuttall
