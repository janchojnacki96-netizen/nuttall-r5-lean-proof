import W5.ThetaB02B20FullCoefficientSummability

/-!
# The genuine (1,2) mixed theta jet and exact B12 certificate polynomial

This moves beyond pure second derivatives. For the numerical
theta coefficient, the (1,2) Taylor polynomial is

  B12(d,q) = -d³/2 + d*q.

The actual (one LEFT, two RIGHT) ordinary Gaussian derivative
is exactly 1!2! = 2 times this polynomial.

The existing PR #58 proof legitimately passes one left derivative
and any fixed number of right derivatives through BOTH the
full square-index n-sum and the positive-half-line Lebesgue
w-integral. Here we specialize it to right order 2 and
identify the pointwise weight with B12, including n=0.

This is a certificate-to-transformed-Gaussian identity only,
not the original normalized Nuttall kernel identification,
and no determinant sign is claimed.
-/

namespace W5
open MeasureTheory

/-- Numerically normalized mixed Taylor coefficient B12. -/
theorem coefficientPolynomial_one_two (d q : ℝ) :
    coefficientPolynomial (1:Fin 5) (2:Fin 5) d q =
      -(d^3)/2+d*q := by
  norm_num [coefficientPolynomial, Finset.sum_range_succ] <;> ring

/-- The symmetric coefficient B21 agrees with the same polynomial. -/
theorem coefficientPolynomial_two_one_via_symmetry (d q : ℝ) :
    coefficientPolynomial (2:Fin 5) (1:Fin 5) d q =
      -(d^3)/2+d*q := by
  rw [coefficientPolynomial_symmetric]
  exact coefficientPolynomial_one_two d q

/-- The actual weighted (1,2) Gaussian jet at the Taylor
origin is precisely 2! times B12(d,q), with every exterior
theta weight, the non-polynomial w-weight and n=0 included. -/
theorem thetaMixedOneRightJetSeriesTerm_two_zero_eq_B12
    (x : ℝ) (n : ℕ) (w : ℝ) :
    thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w =
      if n = 0 then (0:ℝ) else
        let p : ℝ := (n:ℝ)^2
        let d0 : ℝ := (p-1)/x
        2 * (Real.exp (-(p-1)/x^2) *
          (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
            coefficientPolynomial (1:Fin 5) (2:Fin 5)
              (d0+w*x) (p+w*x^2))) := by
  by_cases hn : n = 0
  · simp [thetaMixedOneRightJetSeriesTerm, hn]
  · simp only [thetaMixedOneRightJetSeriesTerm, if_neg hn,
      coefficientPolynomial_one_two]
    dsimp [thetaWeightedGaussianRightMultiplier,
      thetaWeightedGaussianIntegrand, thetaGaussianModel]
    simp only [mul_zero, zero_add, add_zero, sub_zero,
      Real.exp_zero, mul_one]
    ring

/-- GENUINE mixed derivative (1 left, 2 right) of the actual
infinite integrated theta series, not a formal derivative symbol,
equals a single Lebesgue integral of the entire B12 jet series.
All differentiation and sum-integral interchanges are justified
by the existing all-orders mixed-jet Fubini and derivative lemmas. -/
theorem thetaGaussianIntegratedSeries_mixed_one_two_eq_B12_integral_tsum
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    deriv (fun z : ℝ =>
      iteratedDeriv 2
        (fun y : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 =
      ∫ w : ℝ,
        (∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            2 * (Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (1:Fin 5) (2:Fin 5)
                  (d0+w*x) (p+w*x^2))))
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hp := thetaGaussianSummableRightPatch_origin x hx
  have h := thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    2 x 0 0 hx hx1 hp hp
  have hfun :
      (fun w : ℝ =>
        ∑' n : ℕ, thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w) =
      (fun w : ℝ =>
        ∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            2 * (Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (1:Fin 5) (2:Fin 5)
                  (d0+w*x) (p+w*x^2)))) := by
    funext w
    apply tsum_congr
    intro n
    exact thetaMixedOneRightJetSeriesTerm_two_zero_eq_B12 x n w
  rw [hfun] at h
  exact h

end W5
