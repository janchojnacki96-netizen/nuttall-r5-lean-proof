import Nuttall.PsiCompactCell36
import Nuttall.PsiCompactCell37
import Nuttall.PsiCompactCell38
import Nuttall.PsiCompactCell39
import Nuttall.PsiOneCompactBlock40

namespace Nuttall

/-- Join the certified cells starting at 36/128 to the existing right interval. -/
theorem psiOne_compact_from_cell36_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 36/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h36 : t ≤ 37/128
  · exact psiOne_compact_cell36_signed_wronskians p hp t ht h36
  by_cases h37 : t ≤ 38/128
  · exact psiOne_compact_cell37_signed_wronskians p hp t (le_of_not_ge h36) h37
  by_cases h38 : t ≤ 39/128
  · exact psiOne_compact_cell38_signed_wronskians p hp t (le_of_not_ge h37) h38
  by_cases h39 : t ≤ 40/128
  · exact psiOne_compact_cell39_signed_wronskians p hp t (le_of_not_ge h38) h39
  exact psiOne_compact_from_fiveSixteen_signed_wronskians p hp t (by linarith only [lt_of_not_ge h39])

#print axioms psiOne_compact_from_cell36_signed_wronskians

end Nuttall
