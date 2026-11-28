import Nuttall.PsiTwoCompactCell16
import Nuttall.PsiTwoCompactCell17
import Nuttall.PsiTwoCompactCell18
import Nuttall.PsiTwoCompactCell19
import Nuttall.PsiTwoCompactBlock20

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 16. -/
theorem psiTwo_compact_from_cell16_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 16/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h16 : t ≤ 17/128
  · exact psiTwo_compact_cell16_signed_wronskians p hp t ht h16
  by_cases h17 : t ≤ 18/128
  · exact psiTwo_compact_cell17_signed_wronskians p hp t (le_of_not_ge h16) h17
  by_cases h18 : t ≤ 19/128
  · exact psiTwo_compact_cell18_signed_wronskians p hp t (le_of_not_ge h17) h18
  by_cases h19 : t ≤ 20/128
  · exact psiTwo_compact_cell19_signed_wronskians p hp t (le_of_not_ge h18) h19
  exact psiTwo_compact_from_cell20_signed_wronskians p hp t (le_of_not_ge h19)

#print axioms psiTwo_compact_from_cell16_signed_wronskians

end Nuttall
