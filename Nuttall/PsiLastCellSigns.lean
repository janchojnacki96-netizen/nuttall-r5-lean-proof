import Nuttall.PsiLastCellMargin
import Nuttall.PsiCompactCellSigns
import Nuttall.PsiLastCellJetCheck
import Nuttall.PsiLastCellPanelCheck

namespace Nuttall

open W5

private theorem psiOneLastCellCoeffBox_containsReal (l k : ℕ) (hl : l ≤ 12) (hk : k < 25) :
    (psiOneLastCellCoeffBox l k).ContainsReal
      ((1/16:ℝ)^l*(1/512:ℝ)^k/(k.factorial:ℝ) *
        iteratedDeriv (l+k) (psi 1) (255/512)) := by
  have hJ : (match l+k with
    | 0 => psiOneLastCellCornerSnapshot
    | j+1 => psiOneLastCellJetSnapshot j).ContainsReal
      (iteratedDeriv (l+k) (psi 1) (255/512)) := by
    cases hn : l+k with
    | zero => simpa only [iteratedDeriv_zero] using psiOneLastCellCornerSnapshot_containsReal
    | succ j => exact psiOneLastCellJetSnapshot_containsReal j (by omega)
  have h := psiOneCompactCoefficientBoxOfJet_containsReal (radius := (1:ℚ)/512) hJ l k
  have hr : (((1/512:ℚ):ℝ)) = (1:ℝ)/512 := by norm_num
  rw [hr] at h
  exact h

theorem psiOne_compact_last_cell_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 127/256 ≤ t) (hU : t ≤ 1/2) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 512*t-255
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : (255:ℝ)/512+(1/512)*v = t := by dsimp [v]; ring
  have h := psiOne_compact_fixed_cell_signed_wronskians hp (c := 255/512) (h := 1/512)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv
    66 psiOneLastCellBoxes
    (fun k hk i j => psiOneLastCellCoeffBox_containsReal (i.val+j.val) k (by omega) hk)
    psiOneLastCellMargin_checked
  rwa [ht] at h

#print axioms psiOne_compact_last_cell_signed_wronskians

end Nuttall
