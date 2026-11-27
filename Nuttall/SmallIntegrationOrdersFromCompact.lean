import Nuttall.FiveIntegrationOrder
import Nuttall.PhiRankEightTailSigns
import Nuttall.PsiCompactGridPrefix
import Nuttall.PsiEightReplay

namespace Nuttall

/-- A compact certificate for Ψ₁ through order seven gives all three
minima from orders five through seven. -/
theorem kernelIntegrationOrder_eq_one_of_psiOne_compact {r : ℕ} (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7)
    (hcompact : ∀ p ≤ 7, ∀ t : ℝ, 0 ≤ t → t ≤ 53/128 →
      0 < kernelMinorSign p * wronskian (psi 1) p t) :
    kernelIntegrationOrder r = 1 := by
  have h := signRegularWronskians_of_compact_le_eight 1 7 (by decide) hcompact
  have hRR := h.strictReverseSignRegular.reverseSignRegular.mono hr₇
  exact le_antisymm (kernelIntegrationOrder_le_of_reverseSignRegular hRR)
    (one_le_kernelIntegrationOrder_of_five_le hr₅)

/-- Signed Wronskians on each cell of the grid prefix suffice for ranks five to seven. -/
theorem kernelIntegrationOrder_eq_one_of_psiOne_compact_prefix {r : ℕ}
    (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7)
    (hcell : ∀ ab ∈ psiOneCompactPrefix, ∀ p ≤ 7, ∀ t : ℝ, (ab.1:ℝ) ≤ t →
      t ≤ (ab.2:ℝ) → 0 < kernelMinorSign p * wronskian (psi 1) p t) :
    kernelIntegrationOrder r = 1 := by
  apply kernelIntegrationOrder_eq_one_of_psiOne_compact hr₅ hr₇
  intro p hp t ht₀ ht₁
  obtain ⟨ab, hm, ha, hb⟩ := psiOneCompactPrefix_cover ht₀ ht₁
  exact hcell ab hm p hp t ha hb

/-- For order eight, only the Ψ₂ compact certificate is needed in addition
to the analytic tail and the existing negative Ψ₁ witness. -/
theorem kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact
    (hcompact : ∀ p ≤ 8, ∀ t : ℝ, 0 ≤ t → t ≤ 53/128 →
      0 < kernelMinorSign p * wronskian (psi 2) p t) :
    kernelIntegrationOrder 8 = 2 := by
  have h := signRegularWronskians_of_compact_le_eight 2 8 le_rfl hcompact
  exact le_antisymm (kernelIntegrationOrder_le_of_reverseSignRegular
    h.strictReverseSignRegular.reverseSignRegular) two_le_kernelIntegrationOrder_eight

#print axioms kernelIntegrationOrder_eq_one_of_psiOne_compact
#print axioms kernelIntegrationOrder_eq_one_of_psiOne_compact_prefix
#print axioms kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact

end Nuttall
