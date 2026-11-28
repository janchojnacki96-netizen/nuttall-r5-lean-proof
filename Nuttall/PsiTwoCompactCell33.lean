import Nuttall.PsiTwoCompactCell33Margin
import Nuttall.PsiCompactCell33Jets
import Nuttall.PsiTwoCompactAnchor9

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell33Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 9/32 - psiOneDyadicCenter 33
    let rawOne := psiOnePanelBox psiOneCompactAnchor9 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor9 psiTwoCompactAnchor9 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell33Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell33Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell33_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 33/128 ≤ t) (hU : t ≤ 34/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 33 9 (by decide) (by decide +kernel)
    psiOneCompactAnchor9 psiTwoCompactAnchor9 ?_ ?_ psiOneCell33Snapshot psiTwoCell33Corner
    psiOneCell33Inputs_checked psiOneCell33Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell33Basis ?_ ?_ ?_ psiTwoCell33Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor9_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor9_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (33:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (34:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell33_signed_wronskians

end Nuttall
