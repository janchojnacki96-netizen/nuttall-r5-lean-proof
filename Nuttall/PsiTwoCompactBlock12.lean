import Nuttall.PsiTwoCompactCell12
import Nuttall.PsiTwoCompactCell13
import Nuttall.PsiTwoCompactCell14
import Nuttall.PsiTwoCompactCell15
import Nuttall.PsiTwoCompactBlock16

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 12. -/
theorem psiTwo_compact_from_cell12_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 12/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h12 : t ≤ 13/128
  · exact psiTwo_compact_cell12_signed_wronskians p hp t ht h12
  by_cases h13 : t ≤ 14/128
  · exact psiTwo_compact_cell13_signed_wronskians p hp t (le_of_not_ge h12) h13
  by_cases h14 : t ≤ 15/128
  · exact psiTwo_compact_cell14_signed_wronskians p hp t (le_of_not_ge h13) h14
  by_cases h15 : t ≤ 16/128
  · exact psiTwo_compact_cell15_signed_wronskians p hp t (le_of_not_ge h14) h15
  exact psiTwo_compact_from_cell16_signed_wronskians p hp t (le_of_not_ge h15)

#print axioms psiTwo_compact_from_cell12_signed_wronskians

end Nuttall
