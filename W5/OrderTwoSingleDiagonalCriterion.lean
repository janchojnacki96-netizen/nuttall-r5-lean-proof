import W5.NormalizedKernelFirstOrder
import W5.NormalizedKernelZeroth

/-!
# Strict negativity of the ORIGINAL W2 from one diagonal inequality

The genuine normalized coefficient matrix has a positive (0,0)
entry on the theta ray. Since this matrix is symmetric, strict
negativity of just its (1,1) entry forces the determinant negative.
The unconditional determinant normalization identity then forces the
true second Wronskian negative.

This reduction needs only ONE new analytic sign inequality.
It does not assume or assert that this inequality has been proved.
-/

namespace W5

/-- The exact symmetric determinant for the *genuine* normalized
2-by-2 coefficient matrix, with no numerical surrogate. -/
theorem normalizedMatrixTwo_det_symmetric (x : ℝ) :
    (normalizedMatrixTwo x).det =
      analyticCoeff x (0 : Fin 5) (0 : Fin 5) *
        analyticCoeff x (1 : Fin 5) (1 : Fin 5) -
      (analyticCoeff x (0 : Fin 5) (1 : Fin 5)) ^ 2 := by
  rw [Matrix.det_fin_two]
  change
      analyticCoeff x (0 : Fin 5) (0 : Fin 5) *
          analyticCoeff x (1 : Fin 5) (1 : Fin 5) -
        analyticCoeff x (0 : Fin 5) (1 : Fin 5) *
          analyticCoeff x (1 : Fin 5) (0 : Fin 5) =
      analyticCoeff x (0 : Fin 5) (0 : Fin 5) *
        analyticCoeff x (1 : Fin 5) (1 : Fin 5) -
      (analyticCoeff x (0 : Fin 5) (1 : Fin 5)) ^ 2
  rw [← analyticCoeff_zero_one_eq_one_zero x]
  ring

/-- A single strict (1,1) inequality forces the negative sign of
the original Wronskian, because its (0,0) coefficient is strictly
positive and the off-diagonal square is nonnegative. -/
theorem W_two_negative_of_normalized_diagonal_negative
    (t : ℝ) (ht : 0 ≤ t)
    (h11 : analyticCoeff (xOfT t) (1 : Fin 5) (1 : Fin 5) < 0) :
    W 2 t < 0 := by
  have h00 := analyticCoeff_zero_zero_pos_on_ray t ht
  have hcross :
      0 ≤ (analyticCoeff (xOfT t) (0 : Fin 5) (1 : Fin 5)) ^ 2 :=
    sq_nonneg _
  have hproduct :
      analyticCoeff (xOfT t) (0 : Fin 5) (0 : Fin 5) *
        analyticCoeff (xOfT t) (1 : Fin 5) (1 : Fin 5) < 0 :=
    mul_neg_of_pos_of_neg h00 h11
  apply (normalizedMatrixTwo_negative_iff_W_two_negative_exact t ht).mp
  rw [normalizedMatrixTwo_det_symmetric]
  linarith

/-- An identification of only the (1,1) coefficient with the
independently defined theta integral is sufficient; the other
three coefficient-identification obligations are not needed for W2
when the theta (1,1) entry has been certified negative. -/
theorem W_two_negative_of_one_theta_coefficient
    (t : ℝ) (ht : 0 ≤ t)
    (hident :
      analyticCoeff (xOfT t) (1 : Fin 5) (1 : Fin 5) =
        thetaCoefficient (xOfT t) (1 : Fin 5) (1 : Fin 5))
    (hneg : thetaCoefficient (xOfT t) (1 : Fin 5) (1 : Fin 5) < 0) :
    W 2 t < 0 := by
  apply W_two_negative_of_normalized_diagonal_negative t ht
  rw [hident]
  exact hneg

end W5
