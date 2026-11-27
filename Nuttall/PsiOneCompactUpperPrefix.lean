import Nuttall.PsiCompactCell44
import Nuttall.PsiCompactCell45
import Nuttall.PsiCompactCell46
import Nuttall.PsiCompactCell47
import Nuttall.PsiOneCompactRightBlock

namespace Nuttall

/-- Join cells 44–47 to the previously certified right block and the tail. -/
theorem psiOne_compact_upper_prefix_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 11/32 ≤ t) : 0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h₄₄ : t ≤ 45/128
  · exact psiOne_compact_cell44_signed_wronskians p hp t (by linarith only [ht]) h₄₄
  by_cases h₄₅ : t ≤ 46/128
  · exact psiOne_compact_cell45_signed_wronskians p hp t (le_of_not_ge h₄₄) h₄₅
  by_cases h₄₆ : t ≤ 47/128
  · exact psiOne_compact_cell46_signed_wronskians p hp t (le_of_not_ge h₄₅) h₄₆
  by_cases h₄₇ : t ≤ 48/128
  · exact psiOne_compact_cell47_signed_wronskians p hp t (le_of_not_ge h₄₆) h₄₇
  exact psiOne_compact_right_block_signed_wronskians p hp t (by linarith only [lt_of_not_ge h₄₇])

#print axioms psiOne_compact_upper_prefix_signed_wronskians

end Nuttall
