import Nuttall.PsiTwoCompactCell44Margin
import Nuttall.PsiCompactCell44Jets
import Nuttall.PsiTwoCompactAnchor12

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell44Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 12/32 - psiOneDyadicCenter 44
    let rawOne := psiOnePanelBox psiOneCompactAnchor12 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor12 psiTwoCompactAnchor12 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell44Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell44Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell44_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 44/128 ≤ t) (hU : t ≤ 45/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 44 12 (by decide) (by decide +kernel)
    psiOneCompactAnchor12 psiTwoCompactAnchor12 ?_ ?_ psiOneCell44Snapshot psiTwoCell44Corner
    psiOneCell44Inputs_checked psiOneCell44Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell44Basis ?_ ?_ ?_ psiTwoCell44Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor12_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor12_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (44:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (45:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell44_signed_wronskians

end Nuttall
