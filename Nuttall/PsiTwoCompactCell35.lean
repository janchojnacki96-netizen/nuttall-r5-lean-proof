import Nuttall.PsiTwoCompactCell35Margin
import Nuttall.PsiCompactCell35Jets
import Nuttall.PsiTwoCompactAnchor9

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell35Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 9/32 - psiOneDyadicCenter 35
    let rawOne := psiOnePanelBox psiOneCompactAnchor9 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor9 psiTwoCompactAnchor9 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell35Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell35Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell35_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 35/128 ≤ t) (hU : t ≤ 36/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 35 9 (by decide) (by decide +kernel)
    psiOneCompactAnchor9 psiTwoCompactAnchor9 ?_ ?_ psiOneCell35Snapshot psiTwoCell35Corner
    psiOneCell35Inputs_checked psiOneCell35Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell35Basis ?_ ?_ ?_ psiTwoCell35Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor9_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor9_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (35:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (36:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell35_signed_wronskians

end Nuttall
