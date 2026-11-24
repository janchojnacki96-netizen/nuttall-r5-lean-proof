import W5.ThetaActualMixedOneZeroCoefficientBridge

/-!
# Exact B01 coefficient of the genuine transformed Gaussian theta integral series

The original integrated theta Gaussian series is symmetric in its
two Taylor parameters, as established in PR #53. Together with
the genuine left derivative/B10 identification proved in PR #61
and the exact symmetry of the certificate coefficient polynomials,
this identifies the GENUINE right derivative with B01(d,q)=-d
under both the actual n-sum and positive-half-line Lebesgue integral.

This is an unconditional reduction using function equality.
We do not add new summation/differentiation interchange assumptions,
and do not claim the original Nuttall normalized-kernel bridge.
-/

namespace W5
open MeasureTheory

/-- Equality of the genuine right derivative at (u,v)=(0,0)
and the genuine left derivative, by exact functional symmetry
of the full integrated Gaussian theta series. -/
theorem thetaGaussianIntegratedSeries_deriv_right_eq_left_at_origin
    (x : ℝ) :
    deriv
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n z) 0 =
    deriv
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 := by
  have hs :
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n z) =
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) := by
    funext z
    exact thetaGaussianIntegratedSeries_swap x 0 z
  exact congrArg (fun f : ℝ → ℝ => deriv f 0) hs

/-- The first genuine right derivative of the full transformed
Gaussian theta series is the integral of the infinite series
of the certificate polynomial B01(d,q)=-d. -/
theorem thetaGaussianIntegratedSeries_right_deriv_eq_B01_integral_tsum
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    deriv
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n z) 0 =
      ∫ w : ℝ,
        (∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (0:Fin 5) (1:Fin 5)
                  (d0+w*x) (p+w*x^2)))
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have h := thetaGaussianIntegratedSeries_left_deriv_eq_B10_integral_tsum
    x hx hx1
  simp_rw [coefficientPolynomial_symmetric (1:Fin 5) (0:Fin 5)] at h
  exact (thetaGaussianIntegratedSeries_deriv_right_eq_left_at_origin x).trans h

/-- The same exact right-derivative / B01 identity in the
summation-of-integrals convention of the numerical certificate. -/
theorem thetaGaussianIntegratedSeries_right_deriv_eq_B01_tsum_integral
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    deriv
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n z) 0 =
      ∑' n : ℕ,
        ∫ w : ℝ,
          (if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (0:Fin 5) (1:Fin 5)
                  (d0+w*x) (p+w*x^2)))
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have h := thetaGaussianIntegratedSeries_left_deriv_eq_B10_tsum_integral
    x hx hx1
  simp_rw [coefficientPolynomial_symmetric (1:Fin 5) (0:Fin 5)] at h
  exact (thetaGaussianIntegratedSeries_deriv_right_eq_left_at_origin x).trans h

end W5
