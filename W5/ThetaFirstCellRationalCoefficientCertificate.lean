import W5.ThetaFirstCellRationalPolynomialInterval

/-!
# Exact finite rational certificate for ALL first-cell theta w-coefficients

The first-cell theta correction has two affine expressions:
  wx, 1 + w*x².
Each coefficient in w is therefore a rational-coefficient polynomial
in x. Instead of trusting an external polynomial expansion, we build
the bivariate polynomial over Polynomial ℚ and prove a generic
specialization identity by Mathlib's polynomial map homomorphism.

The previous real-sound rational interval evaluator then encloses
the coefficient on 0 <= x <= 1/8. All 5*5*9 rational endpoint tests
are finite and can be proved by native_decide.

No numerical moment bounds, unexplained symbolic identities,
or unproved theta series identities are introduced. The goal is to
discharge the last explicit analytic coefficient premise in the
Gamma/LDL first-cell certificate.
-/

namespace W5

/-- The original first square-index correction viewed as a
polynomial in w whose coefficients are themselves rational
polynomials in x. The scalar formula is the ORIGINAL B_ij
factorial coefficient from the established theta certificate. -/
noncomputable def thetaFirstCellBivariateWPolynomial
    (i j : Fin 5) : Polynomial (Polynomial ℚ) :=
  ∑ t ∈ Finset.range (min i.val j.val + 1),
    Polynomial.C
      (Polynomial.C
        (((-1 : ℚ)^(i.val+j.val-t)) /
          ((Nat.factorial t : ℚ) *
           (Nat.factorial (i.val-t) : ℚ) *
           (Nat.factorial (j.val-t) : ℚ)))) *
      (Polynomial.C (Polynomial.X : Polynomial ℚ) *
          Polynomial.X)^(i.val+j.val-2*t) *
      (Polynomial.C (1 : Polynomial ℚ) +
        Polynomial.C ((Polynomial.X : Polynomial ℚ)^2) *
          Polynomial.X)^t

/-- Mathlib's coefficient map gives an exact rational polynomial
in x for every one of the nine original w-coefficients. -/
noncomputable def thetaFirstCellCoefficientRationalPolynomial
    (i j : Fin 5) (k : ℕ) : Polynomial ℚ :=
  (thetaFirstCellBivariateWPolynomial i j).coeff k

/-- All 25 theta polynomials, for arbitrary real x, are exactly
specializations of a SINGLE rational bivariate construction. -/
theorem thetaFirstCellBivariate_map
    (x : ℝ) (i j : Fin 5) :
    (thetaFirstCellBivariateWPolynomial i j).map
      (Polynomial.eval₂RingHom (Rat.castHom ℝ) x) =
    thetaCorrectionWPolynomial x 1 0 i j := by
  classical
  unfold thetaFirstCellBivariateWPolynomial
    thetaCorrectionWPolynomial
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp [Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow,
    Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_neg]

/-- The rational coefficient polynomial evaluates to the ACTUAL
Mathlib coefficient of the ORIGINAL real theta w-polynomial.
No pointwise sampling assumption or finite interpolation. -/
theorem thetaFirstCellCoefficientRationalPolynomial_eval
    (x : ℝ) (i j : Fin 5) (k : ℕ) :
    (thetaFirstCellCoefficientRationalPolynomial i j k).eval₂
      (Rat.castHom ℝ) x =
      (thetaCorrectionWPolynomial x 1 0 i j).coeff k := by
  let E : Polynomial ℚ →+* ℝ :=
    Polynomial.eval₂RingHom (Rat.castHom ℝ) x
  calc
    _ = ((thetaFirstCellBivariateWPolynomial i j).map E).coeff k := by
      simp [thetaFirstCellCoefficientRationalPolynomial, E]
    _ = (thetaCorrectionWPolynomial x 1 0 i j).coeff k :=
      congrArg (fun P : Polynomial ℝ => P.coeff k)
        (thetaFirstCellBivariate_map x i j)

/-- Rational interval containing the ENTIRE first x-cell. -/
def thetaFirstCellRationalXBox : QInterval :=
  ⟨0, 1/8⟩

/-- Each one of the 225 original w-coefficient functions receives
a precisely computable rational interval using the proved
REAL-semantic polynomial interval evaluator. -/
noncomputable def thetaFirstCellRationalCoefficientInterval
    (i j : Fin 5) (k : ℕ) : QInterval :=
  thetaRationalPolynomialInterval
    (thetaFirstCellCoefficientRationalPolynomial i j k)
    thetaFirstCellRationalXBox

/-- All rational polynomial coefficient intervals contain their
TRUE real coefficients uniformly for the whole first cell. -/
theorem thetaFirstCellRationalCoefficientInterval_containsReal
    (x : ℝ) (hx : 0 ≤ x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) (k : ℕ) :
    QInterval.ContainsReal
      (thetaFirstCellRationalCoefficientInterval i j k)
      ((thetaCorrectionWPolynomial x 1 0 i j).coeff k) := by
  have hxBox : QInterval.ContainsReal thetaFirstCellRationalXBox x := by
    change ((0 : ℚ) : ℝ) ≤ x ∧
      x ≤ ((1/8 : ℚ) : ℝ)
    norm_num
    exact ⟨hx, hxB⟩
  have h := thetaRationalPolynomialInterval_containsReal
    (thetaFirstCellCoefficientRationalPolynomial i j k)
    thetaFirstCellRationalXBox x hxBox
  change QInterval.ContainsReal
    (thetaFirstCellRationalCoefficientInterval i j k)
    ((thetaFirstCellCoefficientRationalPolynomial i j k).eval₂
      (Rat.castHom ℝ) x) at h
  rw [thetaFirstCellCoefficientRationalPolynomial_eval] at h
  exact h

end W5
