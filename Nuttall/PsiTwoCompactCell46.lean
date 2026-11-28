import Nuttall.PsiTwoCompactCell46Margin
import Nuttall.PsiCompactCell46Jets
import Nuttall.PsiTwoCompactAnchor12

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell46Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 12/32 - psiOneDyadicCenter 46
    let rawOne := psiOnePanelBox psiOneCompactAnchor12 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor12 psiTwoCompactAnchor12 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell46Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell46Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell46_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 46/128 ≤ t) (hU : t ≤ 47/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 46 12 (by decide) (by decide +kernel)
    psiOneCompactAnchor12 psiTwoCompactAnchor12 ?_ ?_ psiOneCell46Snapshot psiTwoCell46Corner
    psiOneCell46Inputs_checked psiOneCell46Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell46Basis ?_ ?_ ?_ psiTwoCell46Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor12_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor12_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (46:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (47:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell46_signed_wronskians

end Nuttall
