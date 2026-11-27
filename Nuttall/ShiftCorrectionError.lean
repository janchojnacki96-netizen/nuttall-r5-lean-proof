import Nuttall.ShiftCorrectionNorm
import Nuttall.ShiftHankelCongruence
import Nuttall.ShiftCoreNorm

namespace Nuttall

open scoped Matrix.Norms.L2Operator

/-- The correction is bounded relative to the norm of the core. -/
theorem norm_correctedShiftCore_sub_le {M k : ℕ} (hk : 2*(k-1) ≤ M)
    {u d : ℝ} (hu : 0 ≤ u) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    ‖correctedShiftCore M k u d - shiftCore M k d‖ ≤
      (u/((M:ℝ)+1))*(1+Real.sqrt (Real.pi*((M:ℝ)+1)))*‖shiftCore M k d‖ := by
  let C := shiftCore M k d
  let V := shiftCorrectionMatrix M k d
  let q := u/((M:ℝ)+1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : ‖V.transpose‖ = ‖V‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  have he : correctedShiftCore M k u d - C = -(q • (V*C+C*V.transpose)) := by
    change C - q • (V*C+C*V.transpose) - C = _
    abel
  change ‖correctedShiftCore M k u d - C‖ ≤ q*(1+Real.sqrt (Real.pi*((M:ℝ)+1)))*‖C‖
  rw [he, norm_neg, norm_smul, Real.norm_of_nonneg hq, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hq
  have hV := norm_shiftCorrectionMatrix_le hk hd₀ hd₁
  calc
    _ ≤ ‖V*C‖ + ‖C*V.transpose‖ := norm_add_le _ _
    _ ≤ ‖V‖*‖C‖ + ‖C‖*‖V.transpose‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = (2*‖V‖)*‖C‖ := by rw [ht]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hV]) (norm_nonneg _)

private theorem shiftCorrection_factor_le {N r u B : ℝ}
    (hr : 0 < r) (hrN : r ≤ N) (hu : 0 ≤ u) (huB : u ≤ B) :
    (u/N)*(1+Real.sqrt (Real.pi*N)) ≤ B*(1/r+Real.sqrt (Real.pi/r)) := by
  have hN := hr.trans_le hrN
  have hroot : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have heq : (u/N)*(1+Real.sqrt (Real.pi*N)) = u*(1/N+Real.sqrt (Real.pi/N)) := by
    rw [Real.sqrt_mul Real.pi_nonneg, Real.sqrt_div Real.pi_nonneg]
    have hs : (Real.sqrt N)^2 = N := Real.sq_sqrt hN.le
    field_simp [hN.ne', hroot]
    nlinarith only [congrArg (fun x : ℝ => (u*Real.sqrt Real.pi)*x) hs]
  rw [heq]
  have hdiv : 1/N ≤ 1/r := one_div_le_one_div_of_le hr hrN
  have hp : Real.pi/N ≤ Real.pi/r := div_le_div_of_nonneg_left Real.pi_nonneg hr hrN
  have hs := Real.sqrt_le_sqrt hp
  calc
    _ ≤ u*(1/r+Real.sqrt (Real.pi/r)) := mul_le_mul_of_nonneg_left (add_le_add hdiv hs) hu
    _ ≤ _ := mul_le_mul_of_nonneg_right huB (by positivity)

/-- The correction is uniform for (0le ule B) once (rle M+1). -/
theorem norm_correctedShiftCore_sub_le_uniform {M k : ℕ} (hk : 2*(k-1) ≤ M)
    {r u B d : ℝ} (hr : 0 < r) (hrM : r ≤ (M:ℝ)+1) (hu : 0 ≤ u) (huB : u ≤ B)
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    ‖correctedShiftCore M k u d - shiftCore M k d‖ ≤
      (B*(1/r+Real.sqrt (Real.pi/r)))*‖shiftCore M k d‖ :=
  (norm_correctedShiftCore_sub_le hk hu hd₀ hd₁).trans
    (mul_le_mul_of_nonneg_right (shiftCorrection_factor_le hr hrM hu huB) (norm_nonneg _))

set_option maxHeartbeats 600000 in
/-- Including the correction multiplies the core norm bound by at most (1+E). -/
theorem norm_correctedShiftCore_le_uniform {M k : ℕ} (hk : 2*(k-1) ≤ M)
    {r u B d : ℝ} (hr : 0 < r) (hrM : r ≤ (M:ℝ)+1) (hu : 0 ≤ u) (huB : u ≤ B)
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    ‖correctedShiftCore M k u d‖ ≤
      (1+B*(1/r+Real.sqrt (Real.pi/r)))*‖shiftCore M k d‖ := by
  let A : Matrix (Fin k) (Fin k) ℝ := correctedShiftCore M k u d
  let C : Matrix (Fin k) (Fin k) ℝ := shiftCore M k d
  let E : ℝ := B*(1/r+Real.sqrt (Real.pi/r))
  have hdiff : ‖A-C‖ ≤ E*‖C‖ :=
    norm_correctedShiftCore_sub_le_uniform hk hr hrM hu huB hd₀ hd₁
  have htri : ‖A‖ ≤ ‖C‖+‖A-C‖ := norm_le_norm_add_norm_sub' A C
  have heq : ‖C‖+E*‖C‖ = (1+E)*‖C‖ := by
    rw [add_mul, one_mul]
  exact (htri.trans (add_le_add (le_refl _) hdiff)).trans_eq heq

#print axioms norm_correctedShiftCore_sub_le
#print axioms norm_correctedShiftCore_sub_le_uniform
#print axioms norm_correctedShiftCore_le_uniform

end Nuttall
