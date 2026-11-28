import Nuttall.PsiTwoCompactCell47Margin
import Nuttall.PsiCompactCell47Jets
import Nuttall.PsiTwoCompactAnchor12
import Nuttall.PsiTwoCompactUpperGrid

namespace Nuttall

open W5
open scoped BigOperators

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corners_checked :
    let s := psiOneCell47Snapshot
    let jets := fun j => (s.jets j).asQInterval (2^90)
    let h := 12/32 - psiOneDyadicCenter 47
    let rawOne := psiOnePanelBox psiOneCompactAnchor12 jets 36 h
    let rawTwo := psiTwoPanelBox psiOneCompactAnchor12 psiTwoCompactAnchor12 jets h
    ((s.corner.asQInterval (2^90)).lo ≤ rawOne.lo ∧ rawOne.hi ≤ (s.corner.asQInterval (2^90)).hi) ∧
    ((psiTwoCell47Corner.asQInterval (2^90)).lo ≤ rawTwo.lo ∧
      rawTwo.hi ≤ (psiTwoCell47Corner.asQInterval (2^90)).hi) := by
  decide +kernel

theorem psiTwo_compact_cell47_signed_wronskians (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hL : 47/128 ≤ t) (hU : t ≤ 3/8) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psiTwo_compact_dyadic_snapshot_sound 47 12 (by decide) (by decide +kernel)
    psiOneCompactAnchor12 psiTwoCompactAnchor12 ?_ ?_ psiOneCell47Snapshot psiTwoCell47Corner
    psiOneCell47Inputs_checked psiOneCell47Jets_checked corners_checked.1 corners_checked.2
    psiTwoCell47Basis ?_ ?_ ?_ psiTwoCell47Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiOneCompactAnchor12_containsReal
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using psiTwoCompactAnchor12_containsReal
  · intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> rfl
  · intro i
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · change (47:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (48:ℝ)/128
    linarith only [hU]

theorem psiTwo_compact_from_fortySeven128_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 47/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h : t ≤ 3/8
  · exact psiTwo_compact_cell47_signed_wronskians p hp t ht h
  exact psiTwo_compact_upper_grid_signed_wronskians p hp t (le_of_not_ge h)

#print axioms psiTwo_compact_from_fortySeven128_signed_wronskians

end Nuttall
