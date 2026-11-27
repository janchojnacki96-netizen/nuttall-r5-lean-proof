import Nuttall.PsiFirstCellMargin
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

private noncomputable def firstCellScaledHankel (t : ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  Matrix.of fun i j => (1/16:ℝ)^(i.val+j.val) * iteratedDeriv (i.val+j.val) (psi 1) t

private theorem firstCellScaledLeading_det {p : ℕ} (hp : p ≤ 7) (t : ℝ) :
    (firstCellScaledHankel t |>.submatrix (Fin.castLE hp) (Fin.castLE hp)).det =
      ((Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)).det)^2 *
        wronskian (psi 1) p t := by
  let D := Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)
  let H : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of fun i j => iteratedDeriv (i.val+j.val) (psi 1) t
  have he : (firstCellScaledHankel t).submatrix (Fin.castLE hp) (Fin.castLE hp) =
      D*H*D := by
    ext i j
    simp only [firstCellScaledHankel, Matrix.submatrix_apply, Matrix.of_apply,
      Fin.val_castLE, D, H, Matrix.mul_diagonal, Matrix.diagonal_mul, pow_add]
    ring
  rw [he, Matrix.det_mul, Matrix.det_mul]
  change D.det * H.det * D.det = D.det^2 * H.det
  ring

/-- The first compact cell passes the strict signed-Wronskian test through
rank seven, including its shared endpoints. -/
theorem psiOne_first_cell_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-1
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [ht₀],
    by dsimp [v]; linarith only [ht₁]⟩
  have ht : (1:ℝ)/256 + (1/256)*v = t := by dsimp [v]; ring
  let C (k : ℕ) : Matrix (Fin 7) (Fin 7) ℝ :=
    Matrix.of fun i j => firstCellRealCoeff (i.val+j.val) k
  have hrem (i j : Fin 7) : |firstCellScaledHankel t i j -
      ∑ k ∈ Finset.range 25, C k i j * v^k| ≤ ((1/10^19:ℚ):ℝ) := by
    have h := (psiOne_compact_cell_contains_hankel psiOneFirstCellFixedCorner_containsReal
      (i.val+j.val) (by omega) hv).2
    rw [ht] at h
    simpa only [firstCellScaledHankel, C, firstCellRealCoeff, Matrix.of_apply,
      Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using h
  have h :=
    signed_leading_det_pos_of_compactCertificate hp (d := 25) (by decide)
      (firstCellScaledHankel t) psiOneFirstCellBasis psiOneFirstCellBasis_lower
      psiOneFirstCellBasis_diag v hv (1/10^19) 107 (by norm_num) (by norm_num)
      C psiOneFirstCellReplayBoxes
      (fun k hk i j => firstCellReplayCoeff_containsReal (i.val+j.val) k
        (by omega) (Finset.mem_range.mp hk))
      hrem psiOneFirstCellBasis_rows
      (fun i => (psiOne_first_cell_margin_checked i).trans (by norm_num))
  rw [firstCellScaledLeading_det hp t] at h
  have hD : 0 < (Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)).det := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos (fun _ _ => by positivity)
  have hsq := pow_pos hD 2
  exact (mul_pos_iff_of_pos_left hsq).mp (by
    convert h using 1
    ring)

#print axioms psiOne_first_cell_signed_wronskians

end Nuttall
