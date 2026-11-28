import Nuttall.PsiCompactCell28
import Nuttall.PsiCompactCell29
import Nuttall.PsiCompactCell30
import Nuttall.PsiCompactCell31
import Nuttall.PsiOneCompactBlock32

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 28. -/
theorem psiOne_compact_from_cell28_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 28/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h28 : t ≤ 29/128
  · exact psiOne_compact_cell28_signed_wronskians p hp t ht h28
  by_cases h29 : t ≤ 30/128
  · exact psiOne_compact_cell29_signed_wronskians p hp t (le_of_not_ge h28) h29
  by_cases h30 : t ≤ 31/128
  · exact psiOne_compact_cell30_signed_wronskians p hp t (le_of_not_ge h29) h30
  by_cases h31 : t ≤ 32/128
  · exact psiOne_compact_cell31_signed_wronskians p hp t (le_of_not_ge h30) h31
  exact psiOne_compact_from_cell32_signed_wronskians p hp t (le_of_not_ge h31)

#print axioms psiOne_compact_from_cell28_signed_wronskians

end Nuttall
