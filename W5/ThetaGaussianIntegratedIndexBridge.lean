import W5.ThetaGaussianIntegralFirstDerivative
import W5.ThetaGaussianActualDerivativeProductBound

/-!
# Integrated square-index theta term: a genuine first derivative

This module joins the previously separate proofs:
* the unconditional derivative of one weighted Gaussian w-integral,
* the Gaussian square-index majorant for its differentiated integrand.

The natural index zero is excluded because the weighted formula contains
division by n². The original theta series defines that index to vanish.

This is still an indexwise derivative theorem, NOT differentiation of the
entire theta infinite series or a proof of the Nuttall r=5 sign claim.
-/

namespace W5

open MeasureTheory

/-- The outer theta damping factor is constant in the v-parameter;
thus the single-index integral derivative carries this factor. -/
theorem thetaGaussian_nonzero_index_integral_hasDerivAt_zero
    (x : ℝ) (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu : |u| ≤ 1) (hxu : -(1:ℝ)/2 ≤ x*u) :
    HasDerivAt
      (fun v : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          (∫ w : ℝ,
            thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u v w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))))
      (Real.exp (-((n:ℝ)^2-1)/x^2) *
        (∫ w : ℝ,
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u 0 w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))) (0:ℝ) := by
  have hnR : (1:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast hn
  have hp : 0 < (n:ℝ)^2 := by
    nlinarith
  exact
    (thetaWeightedGaussian_integral_hasDerivAt_zero
      x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u
      hp hu hxu).const_mul
        (Real.exp (-((n:ℝ)^2-1)/x^2))

/-- The actual ordinary derivative of the integrated single-index
theta term has an explicit integral formula at v=0. -/
theorem thetaGaussian_nonzero_index_integral_deriv_zero
    (x : ℝ) (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu : |u| ≤ 1) (hxu : -(1:ℝ)/2 ≤ x*u) :
    deriv
      (fun v : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          (∫ w : ℝ,
            thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u v w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))))
      (0:ℝ) =
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        (∫ w : ℝ,
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u 0 w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  exact (thetaGaussian_nonzero_index_integral_hasDerivAt_zero
    x n hn u hu hxu).deriv

end W5
