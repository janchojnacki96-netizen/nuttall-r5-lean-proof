import Nuttall.PsiCompactReplayWithCutoff
import Nuttall.ZeroIntegrationOrder
import Nuttall.SmallIntegrationOrdersFromCompact
import Nuttall.PhiRankEightTailSigns
import Nuttall.PsiFirstCellSigns
import Nuttall.PsiTwoCompactCell0
import Nuttall.PsiOneCompactBlock8
import Nuttall.PsiTwoCompactBlock12
import Mathlib.Tactic.IntervalCases
import Nuttall.PsiCompactCell1
import Nuttall.PsiCompactCell2
import Nuttall.PsiCompactCell3
import Nuttall.PsiCompactCell4
import Nuttall.PsiCompactCell5
import Nuttall.PsiCompactCell6
import Nuttall.PsiCompactCell7
import Nuttall.PsiTwoCompactCell1
import Nuttall.PsiTwoCompactCell2
import Nuttall.PsiTwoCompactCell3
import Nuttall.PsiTwoCompactCell4
import Nuttall.PsiTwoCompactCell5
import Nuttall.PsiTwoCompactCell6
import Nuttall.PsiTwoCompactCell7
import Nuttall.PsiTwoCompactCell8
import Nuttall.PsiTwoCompactCell9
import Nuttall.PsiTwoCompactCell10
import Nuttall.PsiTwoCompactCell11

namespace Nuttall

private theorem psiOne_complete_compact_signs :
    ∀ p ≤ 7, ∀ t : ℝ, 0 ≤ t → t ≤ 53/128 →
      0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psi_compact_replay_with_origin psiOne_first_cell_signed_wronskians
    psiOne_compact_from_cell8_signed_wronskians ?_
  intro i hi p hp t hleft hright
  have hi_lt := i.isLt
  interval_cases h : i.val
  · exact psiOne_compact_cell1_signed_wronskians p hp t
      (by simpa [h] using hleft) (by simpa [h] using hright)
  · exact psiOne_compact_cell2_signed_wronskians p hp t
      (by simpa [h] using hleft) (by simpa [h] using hright)
  · exact psiOne_compact_cell3_signed_wronskians p hp t
      (by simpa [h] using hleft) (by simpa [h] using hright)
  · exact psiOne_compact_cell4_signed_wronskians p hp t
      (by simpa [h] using hleft) (by simpa [h] using hright)
  · exact psiOne_compact_cell5_signed_wronskians p hp t
      (by simpa [h] using hleft) (by simpa [h] using hright)
  · exact psiOne_compact_cell6_signed_wronskians p hp t
      (by simpa [h] using hleft) (by simpa [h] using hright)
  · exact psiOne_compact_cell7_signed_wronskians p hp t
      (by simpa [h] using hleft) (by simpa [h] using hright)

/-- The order-7 signed Wronskians of the first tail integral on the closed half-line. -/
theorem signRegularWronskians_one_seven : signRegularWronskians 1 7 :=
  signRegularWronskians_of_compact_le_eight 1 7 (by decide) psiOne_complete_compact_signs

private theorem psiTwo_complete_compact_signs :
    ∀ p ≤ 8, ∀ t : ℝ, 0 ≤ t → t ≤ 53/128 →
      0 < kernelMinorSign p * wronskian (psi 2) p t := by
  refine psi_compact_replay_with_origin (n := 12) ?_
    psiTwo_compact_from_cell12_signed_wronskians ?_
  · intro p hp t hleft hright
    exact psiTwo_compact_cell0_signed_wronskians p hp t (by simpa using hleft) hright
  · intro i hi p hp t hleft hright
    have hi_lt := i.isLt
    interval_cases h : i.val
    · exact psiTwo_compact_cell1_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell2_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell3_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell4_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell5_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell6_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell7_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell8_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell9_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell10_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)
    · exact psiTwo_compact_cell11_signed_wronskians p hp t
        (by simpa [h] using hleft) (by simpa [h] using hright)

/-- The order-8 signed Wronskians of the second tail integral on the closed half-line. -/
theorem signRegularWronskians_two_eight : signRegularWronskians 2 8 :=
  signRegularWronskians_of_compact_le_eight 2 8 (by decide) psiTwo_complete_compact_signs

/-- One tail integration is necessary and sufficient in orders five through seven. -/
theorem kernelIntegrationOrder_eq_one_of_five_le_of_le_seven {r : ℕ}
    (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7) : kernelIntegrationOrder r = 1 :=
  kernelIntegrationOrder_eq_one_of_psiOne_compact hr₅ hr₇ psiOne_complete_compact_signs

/-- Exactly two tail integrations are needed in order eight. -/
theorem kernelIntegrationOrder_eight_eq_two : kernelIntegrationOrder 8 = 2 :=
  kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact psiTwo_complete_compact_signs

/-- The exact integration orders in Theorem 2.1 of the preprint. -/
theorem kernelIntegrationOrder_small {r : ℕ} (hr₁ : 1 ≤ r) (hr₈ : r ≤ 8) :
    kernelIntegrationOrder r = if r ≤ 4 then 0 else if r ≤ 7 then 1 else 2 := by
  by_cases hr₄ : r ≤ 4
  · simpa only [ite_eq_left hr₄] using kernelIntegrationOrder_eq_zero_of_le_four hr₄
  by_cases hr₇ : r ≤ 7
  · simpa only [ite_eq_right hr₄, ite_eq_left hr₇] using
      kernelIntegrationOrder_eq_one_of_five_le_of_le_seven (by omega) hr₇
  have he : r = 8 := by omega
  subst r
  simpa only [ite_eq_right hr₄, ite_eq_right hr₇] using kernelIntegrationOrder_eight_eq_two

#print axioms signRegularWronskians_one_seven
#print axioms signRegularWronskians_two_eight
#print axioms kernelIntegrationOrder_small
#print axioms kernelIntegrationOrder_eq_one_of_five_le_of_le_seven
#print axioms kernelIntegrationOrder_eight_eq_two

end Nuttall
