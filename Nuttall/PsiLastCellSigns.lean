import Nuttall.PsiCompactBasisData
import Nuttall.PsiCompactCellCoefficients
import Nuttall.PsiCompactCellSigns
import Nuttall.PsiLastCellJetCheck
import Nuttall.PsiLastCellPanelCheck

namespace Nuttall

open W5

private def psiOneLastCellCoeffBox (l k : ℕ) : QInterval :=
  let J := match l+k with
    | 0 => psiOneLastCellCornerSnapshot
    | j+1 => psiOneLastCellJetSnapshot j
  psiOneCompactCoefficientBoxOfJet (1/512) J l k

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
  simpa only [psiOneLastCellCoeffBox, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    psiOneCompactCoefficientBoxOfJet_containsReal (radius := 1/512) hJ l k

private def psiOneLastCellBoxes (k : ℕ) : Matrix (Fin 7) (Fin 7) QInterval :=
  Matrix.of fun i j => psiOneLastCellCoeffBox (i.val+j.val) k

private def psiOneLastCellMargin (i : Fin 7) : Prop :=
  compactPolynomialRowBound 25 (compactCenteredCoefficientBoxes (psiOneCompactBasis 66)
    psiOneLastCellBoxes) i + 7*((1/10^19)*20000000*20000000) < 7/20

private instance (i : Fin 7) : Decidable (psiOneLastCellMargin i) := by
  unfold psiOneLastCellMargin
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
theorem psiOneLastCellMargin_checked (i : Fin 7) : psiOneLastCellMargin i := by
  fin_cases i <;> decide +kernel

theorem psiOne_compact_last_cell_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 127/256 ≤ t) (hU : t ≤ 1/2) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 512*t-255
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : (255:ℝ)/512+(1/512)*v = t := by dsimp [v]; ring
  have h := psiOne_compact_cell_signed_wronskians hp (c := 255/512) (h := 1/512)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv
    (psiOneCompactBasis 66) (psiOneCompactBasis_lower 66) (psiOneCompactBasis_diagonal_ne_zero 66)
    20000000 (by norm_num) (psiOneCompactBasis_row_le 66) psiOneLastCellBoxes
    (fun k hk i j => psiOneLastCellCoeffBox_containsReal (i.val+j.val) k (by omega) hk)
    (fun i => lt_trans (psiOneLastCellMargin_checked i) (by norm_num : (7/20:ℚ) < 1))
  rwa [ht] at h

#print axioms psiOne_compact_last_cell_signed_wronskians

end Nuttall
