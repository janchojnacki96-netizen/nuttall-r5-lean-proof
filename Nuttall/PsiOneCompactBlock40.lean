import Nuttall.PsiCompactCell40
import Nuttall.PsiCompactCell41
import Nuttall.PsiCompactCell42
import Nuttall.PsiCompactCell43
import Nuttall.PsiOneCompactUpperPrefix

namespace Nuttall

/-- Extend the certified interval to the left end of cell 40. -/
theorem psiOne_compact_from_fiveSixteen_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 5/16 ≤ t) : 0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h₄₀ : t ≤ 41/128
  · exact psiOne_compact_cell40_signed_wronskians p hp t (by linarith only [ht]) h₄₀
  by_cases h₄₁ : t ≤ 42/128
  · exact psiOne_compact_cell41_signed_wronskians p hp t (le_of_not_ge h₄₀) h₄₁
  by_cases h₄₂ : t ≤ 43/128
  · exact psiOne_compact_cell42_signed_wronskians p hp t (le_of_not_ge h₄₁) h₄₂
  by_cases h₄₃ : t ≤ 44/128
  · exact psiOne_compact_cell43_signed_wronskians p hp t (le_of_not_ge h₄₂) h₄₃
  exact psiOne_compact_upper_prefix_signed_wronskians p hp t (by linarith only [lt_of_not_ge h₄₃])

#print axioms psiOne_compact_from_fiveSixteen_signed_wronskians

end Nuttall
