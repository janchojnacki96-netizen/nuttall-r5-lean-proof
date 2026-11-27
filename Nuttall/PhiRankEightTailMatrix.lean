import Nuttall.PhiRankEightGaussianMatrix
import Nuttall.PhiRankEightShiftNorm
import Nuttall.PhiRankEightTailEnvelope

namespace Nuttall

open scoped Matrix.Norms.Operator

/-- Contribution of one square index to the normalized matrix for Φ. -/
noncomputable def phiRankEightTerm (p : ℕ) (X q : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  let G := phiRankEightGaussianMatrix p X q
  let P := phiRankEightCongruenceFactor p X
  q • ((2*q*X) • (P*G*P.transpose) - (3:ℝ) • G)

private theorem phiRankEightTerm_norm_le {p : ℕ} (hp₀ : 0 < p) (hp : p ≤ 8)
    {X q : ℝ} (hX : 16 ≤ X) (hq : 4 ≤ q) :
    ‖phiRankEightTerm p X q‖ ≤ 7*q^2*X*‖phiRankEightGaussianMatrix p X q‖ := by
  let P := phiRankEightCongruenceFactor p X
  let G := phiRankEightGaussianMatrix p X q
  have hq₀ : 0 ≤ q := by linarith
  have hX₀ : 0 ≤ X := by linarith
  have hscalar : 0 ≤ 2*q*X := by positivity
  have hP : ‖P‖ ≤ 7/4 := phiRankEightCongruenceFactor_norm_le hp₀ hp hX
  have hPt : ‖P.transpose‖ ≤ 7/4 := phiRankEightCongruenceFactor_transpose_norm_le hp₀ hp hX
  have hproduct : ‖P*G*P.transpose‖ ≤ (7/4:ℝ)^2*‖G‖ := by
    calc
      _ ≤ ‖P*G‖*‖P.transpose‖ := norm_mul_le _ _
      _ ≤ (‖P‖*‖G‖)*‖P.transpose‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((7/4)*‖G‖)*(7/4) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) hPt (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hqx : (64:ℝ) ≤ q*X :=
    (by norm_num : (64:ℝ) ≤ 4*16).trans (mul_le_mul hq hX (by norm_num) hq₀)
  have hcoeff : 2*q*X*(7/4:ℝ)^2+3 ≤ 7*q*X := by nlinarith only [hqx]
  change ‖q • ((2*q*X) • (P*G*P.transpose) - (3:ℝ) • G)‖ ≤ 7*q^2*X*‖G‖
  rw [norm_smul, Real.norm_of_nonneg hq₀]
  calc
    _ ≤ q*(‖(2*q*X) • (P*G*P.transpose)‖ + ‖(3:ℝ) • G‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hq₀
    _ = q*((2*q*X)*‖P*G*P.transpose‖+3*‖G‖) := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hscalar, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    _ ≤ q*((2*q*X)*((7/4:ℝ)^2*‖G‖)+3*‖G‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hproduct hscalar) le_rfl) hq₀
    _ = q*((2*q*X*(7/4:ℝ)^2+3)*‖G‖) := by ring
    _ ≤ q*((7*q*X)*‖G‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)) hq₀
    _ = _ := by ring

private theorem squareTerm_scale (n X : ℝ) :
    7*(n^2)^2*X * (2^46*(X/16)^7*(n^2/4)^14) =
      (1792*2^46)*(n/2)^32*(X/16)^8 := by ring

theorem phiRankEightSquareTerm_norm_le {p : ℕ} (hp₀ : 0 < p) (hp : p ≤ 8)
    {X : ℝ} (hX : 16 ≤ X) (k : ℕ) :
    ‖phiRankEightTerm p X (((k:ℝ)+2)^2)‖ ≤ phiRankEightTailEnvelope X k := by
  let n : ℝ := (k:ℝ)+2
  have hq : 4 ≤ n^2 := by dsimp [n]; nlinarith only [sq_nonneg (k:ℝ), Nat.cast_nonneg (α := ℝ) k]
  refine (phiRankEightTerm_norm_le hp₀ hp hX hq).trans ?_
  calc
    _ ≤ (7*(n^2)^2*X) * (2^46*(X/16)^7*(n^2/4)^14*Real.exp (-(n^2-1)*X)) :=
      mul_le_mul_of_nonneg_left (phiRankEightGaussianMatrix_norm_le hp hX hq)
        (mul_nonneg (by positivity) (by linarith))
    _ = (1792*2^46)*(n/2)^32*(X/16)^8*Real.exp (-(n^2-1)*X) := by
      rw [← mul_assoc, squareTerm_scale]
    _ = _ := by
      unfold phiRankEightTailEnvelope
      rw [show n^2-1 = (k:ℝ)^2+4*(k:ℝ)+3 by dsimp [n]; ring]
      rw [mul_assoc]

theorem phiRankEightTailMatrix_summable_norm_lt {p : ℕ} (hp₀ : 0 < p) (hp : p ≤ 8)
    {X : ℝ} (hX : 16 ≤ X) :
    Summable (fun k : ℕ => phiRankEightTerm p X (((k:ℝ)+2)^2)) ∧
      ‖∑' k : ℕ, phiRankEightTerm p X (((k:ℝ)+2)^2)‖ < 1/1000 := by
  obtain ⟨hS, hB⟩ := phiRankEightTailEnvelope_summable_le hX
  have hcompare (k : ℕ) := phiRankEightSquareTerm_norm_le hp₀ hp hX k
  have hs := hS.of_nonneg_of_le (fun k : ℕ => norm_nonneg (phiRankEightTerm p X (((k:ℝ)+2)^2))) hcompare
  exact ⟨Summable.of_norm hs, ((norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hcompare hS)).trans_lt hB⟩

#print axioms phiRankEightTailMatrix_summable_norm_lt

end Nuttall
