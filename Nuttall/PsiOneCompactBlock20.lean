import Nuttall.PsiCompactCell20
import Nuttall.PsiCompactCell21
import Nuttall.PsiCompactCell22
import Nuttall.PsiCompactCell23
import Nuttall.PsiOneCompactBlock24

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 20. -/
theorem psiOne_compact_from_cell20_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 20/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h20 : t ≤ 21/128
  · exact psiOne_compact_cell20_signed_wronskians p hp t ht h20
  by_cases h21 : t ≤ 22/128
  · exact psiOne_compact_cell21_signed_wronskians p hp t (le_of_not_ge h20) h21
  by_cases h22 : t ≤ 23/128
  · exact psiOne_compact_cell22_signed_wronskians p hp t (le_of_not_ge h21) h22
  by_cases h23 : t ≤ 24/128
  · exact psiOne_compact_cell23_signed_wronskians p hp t (le_of_not_ge h22) h23
  exact psiOne_compact_from_cell24_signed_wronskians p hp t (le_of_not_ge h23)

#print axioms psiOne_compact_from_cell20_signed_wronskians

end Nuttall
