import Nuttall.PsiTwoCompactCell40
import Nuttall.PsiTwoCompactCell41
import Nuttall.PsiTwoCompactCell42
import Nuttall.PsiTwoCompactCell43
import Nuttall.PsiTwoCompactCell44
import Nuttall.PsiTwoCompactCell45
import Nuttall.PsiTwoCompactCell46
import Nuttall.PsiTwoCompactCell47

namespace Nuttall

/-- Join the certified cells starting at 40/128 to the existing right interval. -/
theorem psiTwo_compact_from_cell40_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 40/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h40 : t ≤ 41/128
  · exact psiTwo_compact_cell40_signed_wronskians p hp t ht h40
  by_cases h41 : t ≤ 42/128
  · exact psiTwo_compact_cell41_signed_wronskians p hp t (le_of_not_ge h40) h41
  by_cases h42 : t ≤ 43/128
  · exact psiTwo_compact_cell42_signed_wronskians p hp t (le_of_not_ge h41) h42
  by_cases h43 : t ≤ 44/128
  · exact psiTwo_compact_cell43_signed_wronskians p hp t (le_of_not_ge h42) h43
  by_cases h44 : t ≤ 45/128
  · exact psiTwo_compact_cell44_signed_wronskians p hp t (le_of_not_ge h43) h44
  by_cases h45 : t ≤ 46/128
  · exact psiTwo_compact_cell45_signed_wronskians p hp t (le_of_not_ge h44) h45
  by_cases h46 : t ≤ 47/128
  · exact psiTwo_compact_cell46_signed_wronskians p hp t (le_of_not_ge h45) h46
  exact psiTwo_compact_from_fortySeven128_signed_wronskians p hp t (le_of_not_ge h46)

#print axioms psiTwo_compact_from_cell40_signed_wronskians

end Nuttall
