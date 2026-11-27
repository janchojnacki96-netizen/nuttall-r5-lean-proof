import Nuttall.PhiJetSeries

namespace Nuttall

open Polynomial
open scoped BigOperators

/-- Integer coefficients of the signed auxiliary jet, in increasing powers. -/
def auxiliaryJetCoeff : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | j + 1, 0 => -5 * auxiliaryJetCoeff j 0
  | j + 1, k + 1 =>
      4 * auxiliaryJetCoeff j k - (5 + 4 * (k + 1 : ℕ)) * auxiliaryJetCoeff j (k + 1)

theorem coeff_auxiliaryDerivativePolynomial (j k : ℕ) :
    (auxiliaryDerivativePolynomial j).coeff k = (auxiliaryJetCoeff j k : ℝ) := by
  induction j generalizing k with
  | zero =>
    by_cases hk : k = 0 <;> simp [auxiliaryDerivativePolynomial, auxiliaryJetCoeff, coeff_one, hk]
  | succ j ih =>
    cases k with
    | zero =>
      simp only [auxiliaryDerivativePolynomial, sub_mul, mul_assoc, coeff_sub,
        coeff_C_mul, coeff_X_mul_zero, auxiliaryJetCoeff, Int.cast_mul, Int.cast_neg,
        Int.cast_ofNat, ih]
      ring
    | succ k =>
      simp only [auxiliaryDerivativePolynomial, sub_mul, mul_assoc, coeff_sub,
        coeff_C_mul, coeff_X_mul, coeff_derivative, auxiliaryJetCoeff, Int.cast_sub,
        Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_one, ih]
      ring

private theorem auxiliaryJetCoeff_eq_zero_of_lt {j k : ℕ} (h : j < k) :
    auxiliaryJetCoeff j k = 0 := by
  induction j generalizing k with
  | zero => simp [auxiliaryJetCoeff, Nat.ne_of_gt h]
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k => rw [auxiliaryJetCoeff, ih (by omega : j < k), ih (by omega : j < k + 1)]
                simp

/-- Rational coefficients of the kernel jet after the auxiliary weight is factored out. -/
def phiJetCoeff (j k : ℕ) : ℚ :=
  ((-1 : ℚ)^j / 2) * ((auxiliaryJetCoeff (j + 1) k : ℚ) - (auxiliaryJetCoeff j k : ℚ))

theorem coeff_phiJetPolynomial (j k : ℕ) : (phiJetPolynomial j).coeff k = (phiJetCoeff j k : ℝ) := by
  simp [phiJetPolynomial, phiJetCoeff, coeff_C_mul, coeff_sub, coeff_auxiliaryDerivativePolynomial]

theorem eval_phiJetPolynomial {j : ℕ} (hj : j ≤ 8) (x : ℝ) :
    (phiJetPolynomial j).eval x = ∑ k ∈ Finset.range 10, (phiJetCoeff j k : ℝ) * x^k := by
  have hd : (phiJetPolynomial j).natDegree ≤ 9 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_phiJetPolynomial]
    simp [phiJetCoeff, auxiliaryJetCoeff_eq_zero_of_lt (show j < k by omega),
      auxiliaryJetCoeff_eq_zero_of_lt (show j + 1 < k by omega)]
  rw [eval_eq_sum_range' (by omega : (phiJetPolynomial j).natDegree < 10)]
  simp only [coeff_phiJetPolynomial]

#print axioms eval_phiJetPolynomial

end Nuttall
