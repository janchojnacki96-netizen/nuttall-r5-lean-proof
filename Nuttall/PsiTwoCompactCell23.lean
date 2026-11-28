import Nuttall.PsiTwoCompactCell23Margin
import Nuttall.PsiCompactCell23Jets
import Nuttall.PsiTwoCompactAnchor6

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell23Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 6/32 - psiOneDyadicCenter 23
    let rawOne := psiOnePanelBox psiOneCompactAnchor6 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor6 psiTwoCompactAnchor6 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell23Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell23Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell23_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 23/128 ≤ t) (hU : t ≤ 24/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 23 6 (by decide) (by decide +kernel)
    psiOneCompactAnchor6 psiTwoCompactAnchor6 ?_ ?_ psiOneCell23Snapshot psiTwoCell23Corner
    psiOneCell23Inputs_checked psiOneCell23Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell23Basis ?_ ?_ ?_ psiTwoCell23Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor6_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor6_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (23:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (24:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell23_signed_wronskians

end Nuttall
