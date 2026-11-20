import W5.ThetaAllCoefficientGenericSplitting
import W5.OrderTwoPolynomialCoefficients

/-!
# Exact 2x2 determinant of the genuine polynomial theta coefficient block

Before numerical certification, exploit a READY-MADE symbolic identity
from Mathlib: `Matrix.det_fin_two`.

The actual numerical certificate coefficients satisfy B00=1,
B01=B10=-d, B11=d²-q. Their leading 2x2 determinant is not
merely bounded: it is EXACTLY -q for every d and q.

For each individual square-index n>0, the original elementary
Gaussian base matrix is a positive scalar multiple of this
polynomial matrix, hence has strictly negative determinant.

IMPORTANT: a sum of matrices with negative determinant need not
have negative determinant. This theorem is an exact, useful
single-index building block, NOT the missing sign of the
complete theta certificate matrix or the Wronskian.
-/

namespace W5

/-- Exact 2x2 determinant of the ORIGINAL certificate polynomials.
This identity is independent of d: the d² term cancels. -/
theorem thetaCoefficientPolynomialTwo_det_exact
    (d q : ℝ) :
    (Matrix.of (fun (i j : Fin 2) =>
      coefficientPolynomial
        (⟨i.val, by omega⟩ : Fin 5)
        (⟨j.val, by omega⟩ : Fin 5) d q)).det = -q := by
  rw [Matrix.det_fin_two]
  change
    coefficientPolynomial 0 0 d q *
      coefficientPolynomial 1 1 d q -
      coefficientPolynomial 0 1 d q *
      coefficientPolynomial 1 0 d q = -q
  rw [coefficientPolynomial_zero_zero,
    coefficientPolynomial_one_one,
    coefficientPolynomial_zero_one,
    coefficientPolynomial_one_zero]
  ring

/-- A scalar multiple of the 2x2 genuine polynomial coefficient
matrix has determinant -(scalar)^2*q. In particular, only the
sign of q matters when the scalar is nonzero. -/
theorem thetaCoefficientPolynomialTwo_scaled_det_exact
    (a d q : ℝ) :
    (Matrix.of (fun (i j : Fin 2) =>
      a * coefficientPolynomial
        (⟨i.val, by omega⟩ : Fin 5)
        (⟨j.val, by omega⟩ : Fin 5) d q)).det =
      -(a^2)*q := by
  rw [Matrix.det_fin_two]
  change
    (a * coefficientPolynomial 0 0 d q) *
      (a * coefficientPolynomial 1 1 d q) -
      (a * coefficientPolynomial 0 1 d q) *
      (a * coefficientPolynomial 1 0 d q) = -(a^2)*q
  rw [coefficientPolynomial_zero_zero,
    coefficientPolynomial_one_one,
    coefficientPolynomial_zero_one,
    coefficientPolynomial_one_zero]
  ring

/-- For every positive square index n, and any real x, the
TRUE original elementary Gaussian theta BASE block for the
single n-th summand has a strictly negative determinant.

This says nothing about the determinant of the sum over n,
where cancellations can change the sign. -/
theorem thetaCertificateBaseTerm_index_two_det_negative
    (x : ℝ) (n : ℕ) (hn : 0 < n) :
    (Matrix.of (fun (i j : Fin 2) =>
      thetaCertificateBaseTerm x
        (⟨i.val, by omega⟩ : Fin 5)
        (⟨j.val, by omega⟩ : Fin 5) n)).det < 0 := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnr : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hp : (0:ℝ) < (n:ℝ)^2 := sq_pos_of_pos hnr
  let a : ℝ := (n:ℝ)^2 * Real.exp (-((n:ℝ)^2-1)/x^2)
  have ha : 0 < a := mul_pos hp (Real.exp_pos _)
  have hmatrix :
      Matrix.of (fun (i j : Fin 2) =>
        thetaCertificateBaseTerm x
          (⟨i.val, by omega⟩ : Fin 5)
          (⟨j.val, by omega⟩ : Fin 5) n) =
      Matrix.of (fun (i j : Fin 2) =>
        a * coefficientPolynomial
          (⟨i.val, by omega⟩ : Fin 5)
          (⟨j.val, by omega⟩ : Fin 5)
          (((n:ℝ)^2-1)/x) ((n:ℝ)^2)) := by
    ext i j
    simp only [Matrix.of_apply, thetaCertificateBaseTerm, if_neg hn0]
    rfl
  rw [hmatrix, thetaCoefficientPolynomialTwo_scaled_det_exact]
  have hpos : 0 < (a^2)*((n:ℝ)^2) :=
    mul_pos (sq_pos_of_pos ha) hp
  linarith

end W5
