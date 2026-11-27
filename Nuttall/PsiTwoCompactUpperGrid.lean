import Nuttall.PsiTwoCompactCell48
import Nuttall.PsiTwoCompactCell49
import Nuttall.PsiTwoCompactCell50
import Nuttall.PsiTwoCompactCell51
import Nuttall.PsiTwoCompactGridReplay

namespace Nuttall

/-- Concatenate all rank-eight compact cells between 3/8 and the analytic tail. -/
theorem psiTwo_compact_upper_grid_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 3/8 ≤ t) : 0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h₄₈ : t ≤ 49/128
  · exact psiTwo_compact_cell48_signed_wronskians p hp t ht h₄₈
  by_cases h₄₉ : t ≤ 25/64
  · exact psiTwo_compact_cell49_signed_wronskians p hp t (le_of_not_ge h₄₈) h₄₉
  by_cases h₅₀ : t ≤ 51/128
  · exact psiTwo_compact_cell50_signed_wronskians p hp t (le_of_not_ge h₄₉) h₅₀
  by_cases h₅₁ : t ≤ 13/32
  · exact psiTwo_compact_cell51_signed_wronskians p hp t (le_of_not_ge h₅₀) h₅₁
  exact psiTwo_compact_right_block_signed_wronskians p hp t (le_of_not_ge h₅₁)

#print axioms psiTwo_compact_upper_grid_signed_wronskians

end Nuttall
