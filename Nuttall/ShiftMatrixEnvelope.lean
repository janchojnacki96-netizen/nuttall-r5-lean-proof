import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Ring.GeomSum

namespace Nuttall

open scoped BigOperators Matrix.Norms.L2Operator

/-- The Euclidean operator norm is bounded by the square root of the sum
of the squares of the entries. -/
theorem norm_matrix_le_sqrt_sum_sq {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) : ‖A‖ ≤ Real.sqrt (∑ i : m, ∑ j : m, (A i j)^2) := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := m) A
  let F := ∑ i : m, ∑ j : m, (A i j)^2
  have hF : 0 ≤ F := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  change ‖T‖ ≤ Real.sqrt F
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) (fun x => ?_)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hF, EuclideanSpace.real_norm_sq_eq (T x),
    EuclideanSpace.real_norm_sq_eq x]
  simp only [T, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, F]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x j))

/-- An entrywise product envelope bounds the operator norm by the squared
Euclidean norm of the envelope vector times its common multiplier. -/
theorem norm_matrix_le_of_entry_envelope {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (v : m → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i j, |A i j| ≤ b*v i*v j) :
    ‖A‖ ≤ b * ∑ i, (v i)^2 := by
  apply (norm_matrix_le_sqrt_sum_sq A).trans
  have hs : 0 ≤ b * ∑ i, (v i)^2 := mul_nonneg hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply (Real.sqrt_le_iff).2 ⟨hs, ?_⟩
  calc
    _ ≤ ∑ i, ∑ j, (b*v i*v j)^2 := by
      refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
    _ = _ := by
      simp only [mul_pow, ← Finset.mul_sum]
      rw [show (∑ i, b^2 * (v i)^2 * ∑ j, (v j)^2) =
          (b^2 * ∑ j, (v j)^2) * ∑ i, (v i)^2 by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      ring

/-- Sum of the squared diagonal weights, bounded by the infinite geometric sum. -/
theorem shift_geometricWeight_sum_le (k : ℕ) {s : ℝ} (hs : 0 ≤ s) (hs₁ : s < 1) :
    (∑ i : Fin k, (s^(k-1-i.val))^2) ≤ 1/(1-s^2) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (s^(k-1-i))^2),
    Finset.sum_range_reflect (fun i => (s^i)^2) k]
  have hp : 0 < 1-s^2 := by nlinarith [mul_pos (sub_pos.2 hs₁) (show 0 < 1+s by linarith)]
  apply (le_div_iff₀ hp).2
  simp_rw [← pow_mul, mul_comm _ 2, pow_mul]
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg (sq_nonneg _) _)

#print axioms norm_matrix_le_sqrt_sum_sq
#print axioms norm_matrix_le_of_entry_envelope
#print axioms shift_geometricWeight_sum_le

end Nuttall
