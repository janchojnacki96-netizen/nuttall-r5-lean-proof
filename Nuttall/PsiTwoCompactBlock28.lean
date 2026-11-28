import Nuttall.PsiTwoCompactCell28
import Nuttall.PsiTwoCompactCell29
import Nuttall.PsiTwoCompactCell30
import Nuttall.PsiTwoCompactCell31
import Nuttall.PsiTwoCompactBlock32

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 28. -/
theorem psiTwo_compact_from_cell28_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 28/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h28 : t ≤ 29/128
  · exact psiTwo_compact_cell28_signed_wronskians p hp t ht h28
  by_cases h29 : t ≤ 30/128
  · exact psiTwo_compact_cell29_signed_wronskians p hp t (le_of_not_ge h28) h29
  by_cases h30 : t ≤ 31/128
  · exact psiTwo_compact_cell30_signed_wronskians p hp t (le_of_not_ge h29) h30
  by_cases h31 : t ≤ 32/128
  · exact psiTwo_compact_cell31_signed_wronskians p hp t (le_of_not_ge h30) h31
  exact psiTwo_compact_from_cell32_signed_wronskians p hp t (le_of_not_ge h31)

#print axioms psiTwo_compact_from_cell28_signed_wronskians

end Nuttall
