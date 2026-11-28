import Nuttall.PsiTwoCompactCell0Margin
import Nuttall.PsiCompactCell0Jets
import Nuttall.PsiTwoCompactAnchor1

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell0Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 1/32 - psiOneDyadicCenter 0
    let rawOne := psiOnePanelBox psiOneCompactAnchor1 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor1 psiTwoCompactAnchor1 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell0Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell0Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell0_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 0/128 ≤ t) (hU : t ≤ 1/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 0 1 (by decide) (by decide +kernel)
    psiOneCompactAnchor1 psiTwoCompactAnchor1 ?_ ?_ psiOneCell0Snapshot psiTwoCell0Corner
    psiOneCell0Inputs_checked psiOneCell0Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell0Basis ?_ ?_ ?_ psiTwoCell0Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor1_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor1_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (0:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (1:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell0_signed_wronskians

end Nuttall
