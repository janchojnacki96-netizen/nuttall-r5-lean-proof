import Nuttall.ShiftedMomentWronskianReduction
import Nuttall.ShiftCoreNorm
import Mathlib.Analysis.SpecificLimits.Normed

namespace Nuttall

open scoped BigOperators Matrix.Norms.L2Operator

/-- Inside the open unit ball around the identity, the determinant stays positive. -/
theorem det_pos_of_matrix_norm_sub_one_lt {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (h : ‖A-1‖ < 1) : 0 < A.det := by
  let f (t : ℝ) := (1 + t • (A-1)).det
  have hf : Continuous f := by
    apply Continuous.matrix_det
    fun_prop
  have hzero : f 0 = 1 := by simp [f]
  have hone : f 1 = A.det := by simp [f, add_comm (1 : Matrix m m ℝ)]
  have hno (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : f t ≠ 0 := by
    have hn : ‖-(t • (A-1))‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt h
    have hu := IsUnit.one_sub_of_norm_lt_one hn
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
    simpa only [sub_neg_eq_add, f] using hd.ne_zero
  by_contra! hdet
  have hm : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := by simp [hzero, hone, hdet]
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num) hf.continuousOn hm
  exact hno t ht he

/-- A matrix at norm distance less than one from the alternating diagonal
has the same determinant sign as that diagonal. -/
theorem signed_det_pos_of_norm_sub_shiftSignMatrix_lt {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (h : ‖A-shiftSignMatrix k‖ < 1) :
    0 < (-1:ℝ)^(k*(k-1)/2)*A.det := by
  let J := shiftSignMatrix k
  have hJnorm : ‖J‖ ≤ 1 := by
    change ‖Matrix.diagonal (fun i : Fin k => (-1:ℝ)^i.val)‖ ≤ 1
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by simp)
  have hJJ : J*J = 1 := by
    change Matrix.diagonal (fun i : Fin k => (-1:ℝ)^i.val) *
      Matrix.diagonal (fun i : Fin k => (-1:ℝ)^i.val) = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← mul_pow]
    norm_num
  have hJdet : J.det = (-1:ℝ)^(k*(k-1)/2) := by
    rw [show J = Matrix.diagonal (fun i : Fin k => (-1:ℝ)^i.val) from rfl, Matrix.det_diagonal,
      Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]
  have hnear : ‖J*A-1‖ < 1 := by
    rw [← hJJ, ← mul_sub]
    exact (Matrix.l2_opNorm_mul _ _).trans_lt
      ((mul_le_of_le_one_left (norm_nonneg _) hJnorm).trans_lt h)
  have hp := det_pos_of_matrix_norm_sub_one_lt (J*A) hnear
  simpa only [Matrix.det_mul, hJdet] using hp

/-- A margin of less than one from the sign matrix certifies positivity
of the ordinary shifted-moment Wronskian off the knots. -/
theorem shiftedMomentWronskian_pos_of_norm_margin {L k : ℕ} (hL : k ≤ L) {u : ℝ}
    (hu₀ : 0 < u) (hu : ∀ n : ℕ, 0 < n → u ≠ thetaKnot n)
    (h : ‖summedCorrectedShiftCore (L+k-2) k u-shiftSignMatrix k‖ < 1) :
    0 < shiftedMomentWronskian L k u :=
  (shiftedMomentWronskian_pos_iff hL hu₀ hu).2
    (signed_det_pos_of_norm_sub_shiftSignMatrix_lt _ h)

#print axioms det_pos_of_matrix_norm_sub_one_lt
#print axioms shiftedMomentWronskian_pos_of_norm_margin

end Nuttall
