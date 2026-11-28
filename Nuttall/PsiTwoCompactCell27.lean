import Nuttall.PsiTwoCompactCell27Margin
import Nuttall.PsiCompactCell27Jets
import Nuttall.PsiTwoCompactAnchor7

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell27Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 7/32 - psiOneDyadicCenter 27
    let rawOne := psiOnePanelBox psiOneCompactAnchor7 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor7 psiTwoCompactAnchor7 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell27Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell27Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell27_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 27/128 ≤ t) (hU : t ≤ 28/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 27 7 (by decide) (by decide +kernel)
    psiOneCompactAnchor7 psiTwoCompactAnchor7 ?_ ?_ psiOneCell27Snapshot psiTwoCell27Corner
    psiOneCell27Inputs_checked psiOneCell27Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell27Basis ?_ ?_ ?_ psiTwoCell27Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor7_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor7_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (27:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (28:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell27_signed_wronskians

end Nuttall
