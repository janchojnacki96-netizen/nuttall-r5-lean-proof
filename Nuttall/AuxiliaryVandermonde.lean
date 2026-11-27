import Nuttall.AuxiliaryDerivativePolynomials
import Mathlib.LinearAlgebra.Vandermonde

namespace Nuttall

open Polynomial
open scoped BigOperators

private theorem auxiliaryDerivativePolynomial_coeff_succ (j k : ℕ) :
    (auxiliaryDerivativePolynomial (j+1)).coeff (k+1) =
      4 * (auxiliaryDerivativePolynomial j).coeff k -
      5 * (auxiliaryDerivativePolynomial j).coeff (k+1) -
      4 * ((auxiliaryDerivativePolynomial j).coeff (k+1) * (k+1 : ℝ)) := by
  simp only [auxiliaryDerivativePolynomial, sub_mul, mul_assoc, coeff_sub,
    coeff_C_mul, coeff_X_mul, coeff_derivative]

/-- The derivative polynomials are triangular in the powers of the theta argument. -/
theorem auxiliaryDerivativePolynomial_degree_coeff (j : ℕ) :
    (auxiliaryDerivativePolynomial j).natDegree ≤ j ∧
      (auxiliaryDerivativePolynomial j).coeff j = (4 : ℝ)^j := by
  induction j with
  | zero => simp [auxiliaryDerivativePolynomial]
  | succ j ih =>
    have hd := ih.1
    constructor
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
      rw [auxiliaryDerivativePolynomial_coeff_succ,
        coeff_eq_zero_of_natDegree_lt (show (auxiliaryDerivativePolynomial j).natDegree < k by omega),
        coeff_eq_zero_of_natDegree_lt (show (auxiliaryDerivativePolynomial j).natDegree < k+1 by omega)]
      ring
    · rw [auxiliaryDerivativePolynomial_coeff_succ, ih.2,
        coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le ih.1), pow_succ]
      ring

/-- Remove the lower-degree polynomial terms in the determinant for a
fixed tuple of theta indices. -/
theorem det_auxiliary_polynomial_eval {p : ℕ} (x : Fin p → ℝ) :
    (Matrix.of (fun (i j : Fin p) => (auxiliaryDerivativePolynomial j.val).eval (x i))).det =
      (Matrix.vandermonde x).det * (∏ j : Fin p, (4 : ℝ)^j.val) := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
    x (fun j => auxiliaryDerivativePolynomial j.val)
    (fun j => (auxiliaryDerivativePolynomial_degree_coeff j.val).1), Matrix.det_mul]
  have htri : (Matrix.of (fun (i j : Fin p) =>
      (auxiliaryDerivativePolynomial j.val).coeff i.val)).IsUpperTriangular := by
    intro i j hij
    exact coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (auxiliaryDerivativePolynomial_degree_coeff j.val).1 hij)
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [Matrix.of_apply, (auxiliaryDerivativePolynomial_degree_coeff _).2]

theorem det_auxiliary_weighted_summands {p : ℕ} (n : Fin p → ℕ) (s : Fin p → ℝ) :
    (Matrix.of (fun (i j : Fin p) =>
      auxiliarySummand (n i) (s i) *
        (auxiliaryDerivativePolynomial j.val).eval (auxiliaryCoordinate (n i) (s i)))).det =
      (∏ i : Fin p, auxiliarySummand (n i) (s i)) *
      (Matrix.vandermonde (fun i => auxiliaryCoordinate (n i) (s i))).det *
      (∏ j : Fin p, (4 : ℝ)^j.val) := by
  let A : Matrix (Fin p) (Fin p) ℝ := Matrix.of (fun (i j : Fin p) =>
    (auxiliaryDerivativePolynomial j.val).eval (auxiliaryCoordinate (n i) (s i)))
  change (Matrix.of (fun (i j : Fin p) => auxiliarySummand (n i) (s i) * A i j)).det = _
  rw [Matrix.det_mul_column]
  have h := det_auxiliary_polynomial_eval (fun i => auxiliaryCoordinate (n i) (s i))
  change A.det = _ at h
  rw [h, mul_assoc]

#print axioms auxiliaryDerivativePolynomial_degree_coeff
#print axioms det_auxiliary_weighted_summands

end Nuttall
