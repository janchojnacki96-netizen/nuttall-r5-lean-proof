import Nuttall.ShiftMatrixEnvelope

namespace Nuttall

open scoped BigOperators Matrix.Norms.L2Operator

/-- A matrix with nonnegative entries contracts by the common bound on its
row and column sums. -/
theorem norm_matrix_le_of_row_col_sum {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (hA : ∀ i j, 0 ≤ A i j) {B : ℝ} (hB : 0 ≤ B)
    (hr : ∀ i, ∑ j, A i j ≤ B) (hc : ∀ j, ∑ i, A i j ≤ B) :
    ‖A‖ ≤ B := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := m) A
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  change ‖T‖ ≤ B
  refine T.opNorm_le_bound hB (fun x => ?_)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq (T x), EuclideanSpace.real_norm_sq_eq x]
  simp only [T, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
  have hrow (i : m) : (∑ j : m, A i j * x j)^2 ≤ (∑ j : m, A i j) * ∑ j : m, A i j * (x j)^2 := by
    have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : m => Real.sqrt (A i j)) (fun j : m => Real.sqrt (A i j) * x j)
    simpa only [← mul_assoc, Real.mul_self_sqrt (hA i _), mul_pow, Real.sq_sqrt (hA i _)] using hs
  calc
    _ ≤ ∑ i : m, (∑ j : m, A i j) * ∑ j : m, A i j * (x j)^2 :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ ≤ ∑ i : m, B * ∑ j : m, A i j * (x j)^2 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hr i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (hA i j) (sq_nonneg _))))
    _ = B * ∑ j : m, (∑ i : m, A i j) * (x j)^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ B * ∑ j : m, B*(x j)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _))) hB
    _ = _ := by rw [← Finset.mul_sum, ← mul_assoc, ← sq]

#print axioms norm_matrix_le_of_row_col_sum

end Nuttall
