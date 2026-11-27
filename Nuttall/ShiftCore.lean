import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- The variables are (w) in the outer polynomial and (z) in its coefficients. -/
noncomputable def bilinearPolynomial (a b c e : ℝ) : (ℝ[X])[X] :=
  monomial 1 (C c + C e * X) + C (C a + C b * X)

/-- The unnormalized coefficient of (w^i z^j) in the (M)-th power. -/
noncomputable def bilinearCoeff (M : ℕ) (a b c e : ℝ) (i j : ℕ) : ℝ :=
  (((bilinearPolynomial a b c e)^M).coeff i).coeff j

/-- Extraction in the outer variable leaves a product of two linear forms. -/
theorem coeff_bilinearPolynomial_pow (M i : ℕ) (a b c e : ℝ) :
    ((bilinearPolynomial a b c e)^M).coeff i =
      (C c + C e * X)^i * (C a + C b * X)^(M-i) * C (M.choose i : ℝ) := by
  classical
  rw [bilinearPolynomial, add_pow]
  simp only [finsetSum_coeff, monomial_pow, one_mul, ← map_pow, ← C_eq_natCast,
    monomial_mul_C, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro n _ hn
    simp [hn]
  · intro hn
    have hi : M < i := by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hn
    simp [Nat.choose_eq_zero_of_lt hi]

/-- The polynomial in the preprint before taking its (M)-th power. -/
theorem bilinearPolynomial_shift (d : ℝ) :
    bilinearPolynomial (1-d) d d (-(1+d)) =
      1 - (X : (ℝ[X])[X]) * C X -
        C (C d) * (1-X) * (1-C X) := by
  unfold bilinearPolynomial
  simp only [← C_mul_X_eq_monomial, map_add, map_sub, map_mul, map_neg, map_one]
  ring

/-- The normalized coefficient matrix (C_d) of Section 4.2. -/
noncomputable def shiftCore (M k : ℕ) (d : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => bilinearCoeff M (1-d) d d (-(1+d)) i.val j.val /
    Real.sqrt ((M.choose i.val : ℝ) * (M.choose j.val : ℝ))

/-- The diagonal sign matrix (J_k). -/
noncomputable def shiftSignMatrix (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun i => (-1 : ℝ)^i.val

theorem bilinearCoeff_shift_zero (M i j : ℕ) :
    bilinearCoeff M 1 0 0 (-1) i j = if i = j then (-1 : ℝ)^i * M.choose i else 0 := by
  unfold bilinearCoeff
  rw [coeff_bilinearPolynomial_pow]
  simp only [map_zero, map_one, zero_mul, add_zero, zero_add, one_pow, mul_one]
  rw [C_mul_X_eq_monomial, monomial_pow, one_mul, monomial_mul_C, coeff_monomial]

/-- At zero shift, the binomial factor cancels on each diagonal entry. -/
theorem shiftCore_zero (M k : ℕ) (hk : k ≤ M+1) :
    shiftCore M k 0 = shiftSignMatrix k := by
  ext i j
  change bilinearCoeff M (1-0) 0 0 (-(1+0)) i.val j.val /
    Real.sqrt ((M.choose i.val : ℝ) * (M.choose j.val : ℝ)) =
    Matrix.diagonal (fun l : Fin k => (-1 : ℝ)^l.val) i j
  rw [sub_zero, add_zero, bilinearCoeff_shift_zero]
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl, Matrix.diagonal_apply_eq, ← sq, Real.sqrt_sq (by positivity)]
    have hi : i.val ≤ M := by have := i.isLt; omega
    have hc : (M.choose i.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
    exact mul_div_cancel_right₀ _ hc
  · have hv : i.val ≠ j.val := fun h' => h (Fin.ext h')
    simp [hv, Matrix.diagonal_apply_ne _ h]

#print axioms coeff_bilinearPolynomial_pow
#print axioms bilinearPolynomial_shift
#print axioms shiftCore_zero

end Nuttall
