import Nuttall.PsiCompactCell24
import Nuttall.PsiCompactCell25
import Nuttall.PsiCompactCell26
import Nuttall.PsiCompactCell27
import Nuttall.PsiOneCompactBlock28

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 24. -/
theorem psiOne_compact_from_cell24_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 24/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h24 : t ≤ 25/128
  · exact psiOne_compact_cell24_signed_wronskians p hp t ht h24
  by_cases h25 : t ≤ 26/128
  · exact psiOne_compact_cell25_signed_wronskians p hp t (le_of_not_ge h24) h25
  by_cases h26 : t ≤ 27/128
  · exact psiOne_compact_cell26_signed_wronskians p hp t (le_of_not_ge h25) h26
  by_cases h27 : t ≤ 28/128
  · exact psiOne_compact_cell27_signed_wronskians p hp t (le_of_not_ge h26) h27
  exact psiOne_compact_from_cell28_signed_wronskians p hp t (le_of_not_ge h27)

#print axioms psiOne_compact_from_cell24_signed_wronskians

end Nuttall
