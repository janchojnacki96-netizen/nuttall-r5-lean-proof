import Nuttall.PsiCompactCell48
import Nuttall.PsiCompactCell49
import Nuttall.PsiCompactCell50
import Nuttall.PsiCompactCell51
import Nuttall.PsiCompactCell52
import Nuttall.PhiRankEightTailSigns

namespace Nuttall

/-- The right five cells meet the analytic tail at 53/128. -/
theorem psiOne_compact_right_block_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 3/8 ≤ t) : 0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h₄₈ : t ≤ 49/128
  · exact psiOne_compact_cell48_signed_wronskians p hp t ht h₄₈
  by_cases h₄₉ : t ≤ 25/64
  · exact psiOne_compact_cell49_signed_wronskians p hp t (le_of_not_ge h₄₈) h₄₉
  by_cases h₅₀ : t ≤ 51/128
  · exact psiOne_compact_cell50_signed_wronskians p hp t (le_of_not_ge h₄₉) h₅₀
  by_cases h₅₁ : t ≤ 13/32
  · exact psiOne_compact_cell51_signed_wronskians p hp t (le_of_not_ge h₅₀) h₅₁
  by_cases h₅₂ : t ≤ 53/128
  · exact psiOne_compact_cell52_signed_wronskians p hp t (le_of_not_ge h₅₁) h₅₂
  exact psi_signed_wronskian_pos_on_compact_tail 1 (hp.trans (by decide)) (le_of_not_ge h₅₂)

#print axioms psiOne_compact_right_block_signed_wronskians

end Nuttall
