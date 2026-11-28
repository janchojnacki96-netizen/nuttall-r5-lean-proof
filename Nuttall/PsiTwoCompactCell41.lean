import Nuttall.PsiTwoCompactCell41Margin
import Nuttall.PsiCompactCell41Jets
import Nuttall.PsiTwoCompactAnchor11

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell41Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 11/32 - psiOneDyadicCenter 41
    let rawOne := psiOnePanelBox psiOneCompactAnchor11 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor11 psiTwoCompactAnchor11 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell41Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell41Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell41_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 41/128 ≤ t) (hU : t ≤ 42/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 41 11 (by decide) (by decide +kernel)
    psiOneCompactAnchor11 psiTwoCompactAnchor11 ?_ ?_ psiOneCell41Snapshot psiTwoCell41Corner
    psiOneCell41Inputs_checked psiOneCell41Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell41Basis ?_ ?_ ?_ psiTwoCell41Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor11_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor11_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (41:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (42:ℝ)/128
    exact hU

#print axioms psiTwo_compact_cell41_signed_wronskians

end Nuttall
