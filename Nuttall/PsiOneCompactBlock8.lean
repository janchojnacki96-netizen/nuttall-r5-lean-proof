import Nuttall.PsiCompactCell8
import Nuttall.PsiCompactCell9
import Nuttall.PsiCompactCell10
import Nuttall.PsiCompactCell11
import Nuttall.PsiOneCompactBlock12

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 8. -/
theorem psiOne_compact_from_cell8_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 8/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h8 : t ≤ 9/128
  · exact psiOne_compact_cell8_signed_wronskians p hp t ht h8
  by_cases h9 : t ≤ 10/128
  · exact psiOne_compact_cell9_signed_wronskians p hp t (le_of_not_ge h8) h9
  by_cases h10 : t ≤ 11/128
  · exact psiOne_compact_cell10_signed_wronskians p hp t (le_of_not_ge h9) h10
  by_cases h11 : t ≤ 12/128
  · exact psiOne_compact_cell11_signed_wronskians p hp t (le_of_not_ge h10) h11
  exact psiOne_compact_from_cell12_signed_wronskians p hp t (le_of_not_ge h11)

#print axioms psiOne_compact_from_cell8_signed_wronskians

end Nuttall
