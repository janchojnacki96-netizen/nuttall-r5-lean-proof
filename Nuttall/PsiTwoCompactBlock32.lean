import Nuttall.PsiTwoCompactCell32
import Nuttall.PsiTwoCompactCell33
import Nuttall.PsiTwoCompactCell34
import Nuttall.PsiTwoCompactCell35
import Nuttall.PsiTwoCompactBlock36

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 32. -/
theorem psiTwo_compact_from_cell32_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 32/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h32 : t ≤ 33/128
  · exact psiTwo_compact_cell32_signed_wronskians p hp t ht h32
  by_cases h33 : t ≤ 34/128
  · exact psiTwo_compact_cell33_signed_wronskians p hp t (le_of_not_ge h32) h33
  by_cases h34 : t ≤ 35/128
  · exact psiTwo_compact_cell34_signed_wronskians p hp t (le_of_not_ge h33) h34
  by_cases h35 : t ≤ 36/128
  · exact psiTwo_compact_cell35_signed_wronskians p hp t (le_of_not_ge h34) h35
  exact psiTwo_compact_from_cell36_signed_wronskians p hp t (le_of_not_ge h35)

#print axioms psiTwo_compact_from_cell32_signed_wronskians

end Nuttall
