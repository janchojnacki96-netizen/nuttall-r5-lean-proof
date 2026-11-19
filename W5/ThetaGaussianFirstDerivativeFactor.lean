import W5.ThetaGaussianUniformDecay

/-!
# First derivatives of the transformed Gaussian, with explicit w dependence

The derivative in v of the Gaussian factor is an affine polynomial in w
times the original Gaussian. This is a concrete step toward finding a
common dominating function for differentiation under the improper w integral.

This module does not assert the interchange of derivatives and integrals.
-/

namespace W5

/-- The coefficient multiplying the first v derivative is affine in w. -/
theorem thetaGaussian_right_derivative_multiplier
    (x p d0 u w : ℝ) :
    -(d0+w*x) - (p+w*x^2)*u =
      (-d0-p*u) - w*x*(1+x*u) := by
  ring

/-- Exact first derivative of the transformed Gaussian. -/
theorem thetaGaussian_right_deriv_at
    (x p d0 u v w : ℝ) :
    deriv (fun z : ℝ =>
      thetaGaussianModel (d0+w*x) (p+w*x^2) u z) v =
      ((-d0-p*u)-w*x*(1+x*u)) *
        thetaGaussianModel (d0+w*x) (p+w*x^2) u v := by
  rw [(thetaGaussianModel_right_hasDerivAt
    (d0+w*x) (p+w*x^2) u v).deriv]
  congr 1
  ring

/-- The derivative of the w-weighted Gaussian factors into a
w-independent exponential, an affine w multiplier, and damping. -/
theorem thetaGaussian_weighted_right_deriv_factor
    (x p d0 u v w : ℝ) :
    Real.exp (-w) *
      deriv (fun z : ℝ =>
        thetaGaussianModel (d0+w*x) (p+w*x^2) u z) v =
      ((-d0-p*u)-w*x*(1+x*u)) *
        (Real.exp (-d0*(u+v)-p*u*v) *
          Real.exp (-w*(1+x*u)*(1+x*v))) := by
  rw [thetaGaussian_right_deriv_at]
  rw [← thetaGaussian_weight_factor]
  ring

end W5
