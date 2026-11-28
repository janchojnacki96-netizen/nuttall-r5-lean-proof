import Nuttall.PsiCompactCell12
import Nuttall.PsiCompactCell13
import Nuttall.PsiCompactCell14
import Nuttall.PsiCompactCell15
import Nuttall.PsiOneCompactBlock16

namespace Nuttall

/-- Extend the right interval to the left endpoint of cell 12. -/
theorem psiOne_compact_from_cell12_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht : 12/128 ≤ t) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  by_cases h12 : t ≤ 13/128
  · exact psiOne_compact_cell12_signed_wronskians p hp t ht h12
  by_cases h13 : t ≤ 14/128
  · exact psiOne_compact_cell13_signed_wronskians p hp t (le_of_not_ge h12) h13
  by_cases h14 : t ≤ 15/128
  · exact psiOne_compact_cell14_signed_wronskians p hp t (le_of_not_ge h13) h14
  by_cases h15 : t ≤ 16/128
  · exact psiOne_compact_cell15_signed_wronskians p hp t (le_of_not_ge h14) h15
  exact psiOne_compact_from_cell16_signed_wronskians p hp t (le_of_not_ge h15)

#print axioms psiOne_compact_from_cell12_signed_wronskians

end Nuttall
