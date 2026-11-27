import Nuttall.ShiftCorrection
import Nuttall.ShiftReflectionOrthogonality
import Mathlib.LinearAlgebra.Matrix.Block

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- One column of the generating transformation in a single variable. -/
noncomputable def shiftHankelBasisTerm (M a : ℕ) (u : ℝ) : ℝ[X] :=
  C (u^a / (a.factorial : ℝ)) * (X^a * (1-X)^(M-a))

theorem shiftHankelBasisTerm_coeff_eq_zero {M a i : ℕ} (u : ℝ) (h : i < a) :
    (shiftHankelBasisTerm M a u).coeff i = 0 := by
  simp [shiftHankelBasisTerm, coeff_C_mul, coeff_X_pow_mul', h.not_ge]

theorem shiftHankelBasisTerm_coeff_diag (M a : ℕ) (u : ℝ) :
    (shiftHankelBasisTerm M a u).coeff a = u^a / (a.factorial : ℝ) := by
  simp [shiftHankelBasisTerm, coeff_C_mul, coeff_X_pow_mul', coeff_zero_eq_eval_zero]

/-- The triangular coefficient matrix, with division by the square root
of the row binomial coefficient. -/
noncomputable def shiftHankelBasis (M k : ℕ) (u : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i a => (shiftHankelBasisTerm M a.val u).coeff i.val /
    Real.sqrt (M.choose i.val : ℝ)

theorem shiftHankelBasis_lowerTriangular (M k : ℕ) (u : ℝ) :
    (shiftHankelBasis M k u).IsLowerTriangular := by
  intro i a h
  change i.val < a.val at h
  simp [shiftHankelBasis, shiftHankelBasisTerm_coeff_eq_zero _ h]

theorem det_shiftHankelBasis_pos {M k : ℕ} (hk : k ≤ M+1) {u : ℝ} (hu : 0 < u) :
    0 < (shiftHankelBasis M k u).det := by
  rw [Matrix.det_of_isLowerTriangular _ (shiftHankelBasis_lowerTriangular M k u)]
  apply Finset.prod_pos
  intro i _
  simp only [shiftHankelBasis, Matrix.of_apply, shiftHankelBasisTerm_coeff_diag]
  have hi := i.isLt
  have hchoose : (0 : ℝ) < M.choose i.val := by exact_mod_cast Nat.choose_pos (show i.val ≤ M by omega)
  exact div_pos (div_pos (pow_pos hu _) (by positivity)) (Real.sqrt_pos.2 hchoose)

/-- Polynomial encoding of the two independent triangular changes of basis. -/
noncomputable def shiftHankelPolynomial (M k : ℕ) (u : ℝ) (H : Matrix (Fin k) (Fin k) ℝ) :
    (ℝ[X])[X] :=
  ∑ a : Fin k, ∑ b : Fin k,
    C (C (H a b)) * separatedProduct (shiftHankelBasisTerm M a.val u) (shiftHankelBasisTerm M b.val u)

/-- Extracting the low coefficients is exactly matrix congruence. -/
theorem normalizedShiftCoefficients_hankelPolynomial (M k : ℕ) (u : ℝ)
    (H : Matrix (Fin k) (Fin k) ℝ) :
    normalizedShiftCoefficients M k (shiftHankelPolynomial M k u H) =
      shiftHankelBasis M k u * H * (shiftHankelBasis M k u).transpose := by
  ext i j
  simp only [normalizedShiftCoefficients, shiftHankelPolynomial, shiftHankelBasis,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, finsetSum_coeff, coeff_C_mul,
    coeff_separatedProduct, Finset.sum_mul, Finset.sum_div, Real.sqrt_mul (Nat.cast_nonneg _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem shiftHankelPolynomial_sub (M k : ℕ) (u : ℝ)
    (H K : Matrix (Fin k) (Fin k) ℝ) :
    shiftHankelPolynomial M k u (H-K) =
      shiftHankelPolynomial M k u H - shiftHankelPolynomial M k u K := by
  simp only [shiftHankelPolynomial, Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

#print axioms det_shiftHankelBasis_pos
#print axioms normalizedShiftCoefficients_hankelPolynomial

end Nuttall
