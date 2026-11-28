import Nuttall.PsiTwoCompactCell36
import Nuttall.PsiTwoCompactCell37
import Nuttall.PsiTwoCompactCell38
import Nuttall.PsiTwoCompactCell39
import Nuttall.PsiTwoCompactBlock40

namespace Nuttall

/-- Join the certified cells starting at 36/128 to the existing right interval. -/
theorem psiTwo_compact_from_cell36_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 36/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h36 : t ≤ 37/128
  · exact psiTwo_compact_cell36_signed_wronskians p hp t ht h36
  by_cases h37 : t ≤ 38/128
  · exact psiTwo_compact_cell37_signed_wronskians p hp t (le_of_not_ge h36) h37
  by_cases h38 : t ≤ 39/128
  · exact psiTwo_compact_cell38_signed_wronskians p hp t (le_of_not_ge h37) h38
  by_cases h39 : t ≤ 40/128
  · exact psiTwo_compact_cell39_signed_wronskians p hp t (le_of_not_ge h38) h39
  exact psiTwo_compact_from_cell40_signed_wronskians p hp t (le_of_not_ge h39)

#print axioms psiTwo_compact_from_cell36_signed_wronskians

end Nuttall
