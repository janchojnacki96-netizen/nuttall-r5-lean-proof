import Nuttall.PsiFirstCellMargin
import Nuttall.PsiCompactCellSigns
import Nuttall.PsiFirstCellCornerCheck
import Nuttall.PsiFirstCellJetCheck

namespace Nuttall

open W5
open scoped BigOperators

private noncomputable def firstCellRealCoeff (l k : ℕ) : ℝ :=
  (1/16:ℝ)^l * (1/256:ℝ)^k / (k.factorial:ℝ) * iteratedDeriv (l+k) (psi 1) (1/256)

private theorem firstCellReplayCoeff_containsReal (l k : ℕ) (hl : l ≤ 12) (hk : k < 25) :
    (psiOneFirstCellReplayCoeffBox l k).ContainsReal (firstCellRealCoeff l k) := by
  have hs : QInterval.ContainsReal
      (QInterval.point ((1/16:ℚ)^l * (1/256:ℚ)^k / (k.factorial:ℚ)))
      ((1/16:ℝ)^l * (1/256:ℝ)^k / (k.factorial:ℝ)) := by
    simp only [QInterval.ContainsReal, QInterval.point, Rat.cast_pow, Rat.cast_mul,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, le_refl, and_self]
  unfold psiOneFirstCellReplayCoeffBox firstCellRealCoeff
  apply compactRoundInterval_containsReal (by positivity)
  apply QInterval.mul_containsReal hs
  cases h : l+k with
  | zero => simpa only [iteratedDeriv_zero] using psiOneFirstCellFixedCorner_containsReal
  | succ j => exact psiOneFirstCellDyadicJetBox_containsReal j (by omega)

/-- The first compact cell passes the strict signed-Wronskian test through
rank seven, including its shared endpoints. -/
theorem psiOne_first_cell_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-1
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [ht₀],
    by dsimp [v]; linarith only [ht₁]⟩
  have ht : (1:ℝ)/256 + (1/256)*v = t := by dsimp [v]; ring
  have h := psiOne_compact_cell_signed_wronskians hp (c := 1/256) (h := 1/256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv
    psiOneFirstCellBasis psiOneFirstCellBasis_lower psiOneFirstCellBasis_diag 107 (by norm_num)
    psiOneFirstCellBasis_rows psiOneFirstCellReplayBoxes
    (fun k hk i j => firstCellReplayCoeff_containsReal (i.val+j.val) k (by omega) hk)
    (fun i => (psiOne_first_cell_margin_checked i).trans (by norm_num))
  rwa [ht] at h

#print axioms psiOne_first_cell_signed_wronskians

end Nuttall
