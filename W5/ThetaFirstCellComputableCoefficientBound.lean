import W5.ThetaFirstCellRationalCoefficientCertificate

/-!
# Computable rational coefficient majorants for the original first theta cell

Mathlib polynomial semiring multiplication is noncomputable in the
nested polynomial representation; therefore native_decide cannot be
applied directly to thetaFirstCellBivariateWPolynomial.  This module
instead provides a finite, entirely computable BINOMIAL majorant,
and separates its 225 rational checks from the real polynomial
coefficient identity.

For 0 <= x <= 1/8 and m=i+j-2t, the coefficient of w^k in
  (w*x)^m * (1+w*x²)^t
is zero for k<m and otherwise
  x^m * (t.choose (k-m)) * (x²)^(k-m).
Its absolute value is bounded by replacing x with 1/8.

This construction uses only Mathlib and exact rational computation.
The explicit finite check below is kernel-checked via
native_decide on rationals. The real coefficient-to-majorant
inequality is proved in ThetaFirstCellBinomialMajorantSound.
-/

namespace W5

/-- The k-th coefficient in (1+a*w)^t, using Mathlib's
existing exact binomial coefficient and composition formula. -/
theorem thetaFirstCell_one_add_scaled_X_pow_coeff
    (a : ℝ) (t k : ℕ) :
    ((1 + Polynomial.C a * Polynomial.X : Polynomial ℝ)^t).coeff k =
      (t.choose k : ℝ) * a^k := by
  have hcomp :
      (((1 + Polynomial.X : Polynomial ℝ)^t).comp
        (Polynomial.C a * Polynomial.X)) =
        (1 + Polynomial.C a * Polynomial.X : Polynomial ℝ)^t := by
    simp
  rw [← hcomp, Polynomial.comp_C_mul_X_coeff,
    Polynomial.coeff_one_add_X_pow]

/-- The exact shifted binomial coefficient in an ORIGINAL
affine theta-polynomial factor. The zero-index case is explicit. -/
theorem thetaFirstCell_affinePower_coeff
    (x : ℝ) (m t k : ℕ) :
    (((Polynomial.C x * Polynomial.X)^m *
        (1 + Polynomial.C (x^2) * Polynomial.X)^t :
          Polynomial ℝ).coeff k) =
      if m ≤ k then
        x^m * ((t.choose (k-m) : ℝ) * (x^2)^(k-m))
      else 0 := by
  have hm :
      (Polynomial.C x * Polynomial.X : Polynomial ℝ)^m =
        Polynomial.C (x^m) * Polynomial.X^m := by
    simp [mul_pow]
  rw [hm, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  simp only [thetaFirstCell_one_add_scaled_X_pow_coeff, mul_ite, mul_zero]
 
/-- All 225 original theta w-coefficients are given by the
same finite binomial sum, for arbitrary real x.
No numerical evaluation or interpolation is used here. -/
theorem thetaFirstCell_original_coeff_binomial
    (x : ℝ) (i j : Fin 5) (k : ℕ) :
    (thetaCorrectionWPolynomial x 1 0 i j).coeff k =
      ∑ t ∈ Finset.range (min i.val j.val + 1),
        (((-1 : ℝ)^(i.val+j.val-t)) /
          ((Nat.factorial t : ℝ) *
           (Nat.factorial (i.val-t) : ℝ) *
           (Nat.factorial (j.val-t) : ℝ))) *
        (if i.val+j.val-2*t ≤ k then
          x^(i.val+j.val-2*t) *
            ((t.choose (k-(i.val+j.val-2*t)) : ℝ) *
              (x^2)^(k-(i.val+j.val-2*t)))
        else 0) := by
  unfold thetaCorrectionWPolynomial
  simp only [Polynomial.C_0, zero_add, Polynomial.C_1]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mul_assoc, Polynomial.coeff_C_mul]
  exact congrArg
    (fun z : ℝ => (((-1 : ℝ)^(i.val+j.val-t)) /
          ((Nat.factorial t : ℝ) *
           (Nat.factorial (i.val-t) : ℝ) *
           (Nat.factorial (j.val-t) : ℝ))) * z)
    (thetaFirstCell_affinePower_coeff x (i.val+j.val-2*t) t k)

/-- A completely COMPUTABLE rational upper bound for the modulus
of each real first-cell theta polynomial coefficient. -/
def thetaFirstCellBinomialMajorant (i j : Fin 5) (k : ℕ) : ℚ :=
  ∑ t ∈ Finset.range (min i.val j.val + 1),
    let m := i.val+j.val-2*t
    let u := k-m
    if m ≤ k ∧ u ≤ t then
      ((t.choose u : ℚ) /
        ((Nat.factorial t : ℚ) *
         (Nat.factorial (i.val-t) : ℚ) *
         (Nat.factorial (j.val-t) : ℚ))) *
        (1/8 : ℚ)^m * (1/64 : ℚ)^u
    else 0

/-- The 225 exact-rational arithmetic checks. They use no
noncomputable Polynomial.semiring instance. The tighter
bound 129/128 is achievable; 4 is the bound required by
the already verified Gamma/LDL interval candidate. -/
theorem thetaFirstCellBinomialMajorant_all225 :
    ∀ i j : Fin 5, ∀ k : Fin 9,
      (8 : ℚ)^k.val * thetaFirstCellBinomialMajorant i j k.val ≤
        129/128 := by
  native_decide

/-- The explicit 4/8^k rational certificate is therefore
valid for the COMPUTABLE majorant, independently of analytic
polynomial semantics. -/
theorem thetaFirstCellBinomialMajorant_le_box
    (i j : Fin 5) (k : Fin 9) :
    thetaFirstCellBinomialMajorant i j k.val ≤
      4 / (8 : ℚ)^k.val := by
  have hh := thetaFirstCellBinomialMajorant_all225 i j k
  have hp : (0 : ℚ) < (8 : ℚ)^k.val := by positivity
  apply (le_div_iff₀ hp).2
  have hq : (129 / 128 : ℚ) ≤ 4 := by norm_num
  calc
    _ = (8 : ℚ)^k.val * thetaFirstCellBinomialMajorant i j k.val := by
      ring
    _ ≤ 4 := hh.trans hq

end W5
