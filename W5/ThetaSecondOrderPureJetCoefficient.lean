import W5.ThetaLeadingTwoActualJetMatrixBridge

/-!
# Genuine second derivatives of the transformed theta series and B02/B20

The preceding exact leading 2x2 matrix identities are now extended
beyond the first-order indices, starting with the (0,2)/(2,0)
polynomial coefficients. The certificate stores *Taylor
coefficients*, so B02(d,q)=B20(d,q)=d²/2, whereas the genuine
second ordinary derivative of the Gaussian is d²=2! B02.

The all-orders dominated-differentiation and Fubini theorems
already in the repository justify differentiating the FULL
infinite theta Gaussian series twice; no new analytic
interchange is postulated here.

These are identities for the transformed Gaussian model.
The original normalized Nuttall kernel and determinant signs
remain separate, unproved bridges.
-/

namespace W5
open MeasureTheory

/-- Exact second-order pure-right Taylor coefficient: 2! in the
denominator is essential to match the numerical certificate. -/
theorem coefficientPolynomial_zero_two (d q : ℝ) :
    coefficientPolynomial (0 : Fin 5) (2 : Fin 5) d q = d^2/2 := by
  norm_num [coefficientPolynomial, Finset.sum_range_succ] <;> ring

/-- Exact symmetry for the pure-left second-order coefficient. -/
theorem coefficientPolynomial_two_zero (d q : ℝ) :
    coefficientPolynomial (2 : Fin 5) (0 : Fin 5) d q = d^2/2 := by
  rw [coefficientPolynomial_symmetric]
  exact coefficientPolynomial_zero_two d q

/-- Exact pointwise correspondence between the ACTUAL second
right Gaussian jet and 2! times the B02 coefficient polynomial.
This includes the exterior square-index damping, the genuine
w-weight and the n=0 convention. -/
theorem thetaHigherRightJetSeriesTerm_two_zero_eq_B02
    (x : ℝ) (n : ℕ) (w : ℝ) :
    thetaHigherRightJetSeriesTerm 2 x 0 0 n w =
      if n = 0 then (0:ℝ) else
        let p : ℝ := (n:ℝ)^2
        let d0 : ℝ := (p-1)/x
        2 * (Real.exp (-(p-1)/x^2) *
          (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
            coefficientPolynomial (0:Fin 5) (2:Fin 5)
              (d0+w*x) (p+w*x^2))) := by
  by_cases hn : n = 0
  · simp [thetaHigherRightJetSeriesTerm, hn]
  · simp only [thetaHigherRightJetSeriesTerm, if_neg hn,
      thetaWeightedGaussianRightJet,
      coefficientPolynomial_zero_two]
    dsimp [thetaWeightedGaussianRightMultiplier,
      thetaWeightedGaussianIntegrand, thetaGaussianModel]
    simp only [mul_zero, zero_add, add_zero, sub_zero,
      Real.exp_zero, mul_one]
    ring

/-- The GENUINE second right derivative of the complete
infinite transformed theta Gaussian series is the Lebesgue
integral of the complete second-right Gaussian jet series. -/
theorem thetaGaussianIntegratedSeries_second_right_eq_integral_tsum
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    iteratedDeriv 2
      (fun y : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n y) 0 =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaHigherRightJetSeriesTerm 2 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hp := thetaGaussianSummableRightPatch_origin x hx
  exact thetaGaussianIntegratedSeries_iteratedDeriv_eq_integral_tsum
    2 x 0 0 hx hx1 hz hp

/-- The genuine second left derivative has the SAME exact
Gaussian-jet integral representation, by the previously proved
symmetry of the entire transformed theta series. -/
theorem thetaGaussianIntegratedSeries_second_left_eq_integral_tsum
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    iteratedDeriv 2
      (fun y : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x y n 0) 0 =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaHigherRightJetSeriesTerm 2 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hp := thetaGaussianSummableRightPatch_origin x hx
  simpa only [thetaHigherLeftJetSeriesTerm] using
    (thetaGaussianIntegratedSeries_iteratedDeriv_left_eq_integral_tsum
      2 x 0 0 hx hx1 hz hp)

/-- The actual second right derivative of the full transformed
theta series has a pointwise B02 integral-series representation.
In particular the coefficient-to-derivative factor is exactly 2!. -/
theorem thetaGaussianIntegratedSeries_second_right_eq_B02_integral_tsum
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    iteratedDeriv 2
      (fun y : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n y) 0 =
      ∫ w : ℝ,
        (∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            2 * (Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (0:Fin 5) (2:Fin 5)
                  (d0+w*x) (p+w*x^2))))
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  rw [thetaGaussianIntegratedSeries_second_right_eq_integral_tsum
    x hx hx1]
  congr 1
  funext w
  apply tsum_congr
  intro n
  exact thetaHigherRightJetSeriesTerm_two_zero_eq_B02 x n w

end W5
