import Nuttall.PsiCompactCell32
import Nuttall.PsiCompactCell33
import Nuttall.PsiCompactCell34
import Nuttall.PsiCompactCell35
import Nuttall.PsiOneCompactBlock36

namespace Nuttall

/-- Join the certified cells starting at 32/128 to the existing right interval. -/
theorem psiOne_compact_from_cell32_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 32/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h32 : t ≤ 33/128
  · exact psiOne_compact_cell32_signed_wronskians p hp t ht h32
  by_cases h33 : t ≤ 34/128
  · exact psiOne_compact_cell33_signed_wronskians p hp t (le_of_not_ge h32) h33
  by_cases h34 : t ≤ 35/128
  · exact psiOne_compact_cell34_signed_wronskians p hp t (le_of_not_ge h33) h34
  by_cases h35 : t ≤ 36/128
  · exact psiOne_compact_cell35_signed_wronskians p hp t (le_of_not_ge h34) h35
  exact psiOne_compact_from_cell36_signed_wronskians p hp t (le_of_not_ge h35)

#print axioms psiOne_compact_from_cell32_signed_wronskians

end Nuttall
