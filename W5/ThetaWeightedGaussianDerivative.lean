import W5.ThetaGaussianNeighborhoodEnvelope

/-!
# Ordinary derivative of the whole weighted theta Gaussian integrand

The quarter-root factor and exp(-w) are constant in v.
This is the genuine HasDerivAt prerequisite for differentiating
a single theta w-integral under the integral sign.

The uniform bound is transferred from the Gaussian derivative to
the derivative of the full integrand, not postulated as a hypothesis.
No derivative/integral or derivative/tsum exchange is asserted here.
-/

namespace W5

/-- The w-integrand appearing in the transformed theta coefficient.
Here x,p,d0,u are fixed, while v is the differentiation coordinate. -/
noncomputable def thetaWeightedGaussianIntegrand
    (x p d0 u v w : ℝ) : ℝ :=
  Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
    thetaGaussianModel (d0+w*x) (p+w*x^2) u v

/-- The actual first derivative of the *entire weighted integrand*.
This is an ordinary real HasDerivAt theorem, with no integral
or infinite series present. -/
theorem thetaWeightedGaussian_hasDerivAt_right
    (x p d0 u v w : ℝ) :
    HasDerivAt
      (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 u z w)
      (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        (((-d0-p*u)-w*x*(1+x*u)) *
          thetaGaussianModel (d0+w*x) (p+w*x^2) u v)) v := by
  have h :=
    (thetaGaussianModel_right_hasDerivAt
      (d0+w*x) (p+w*x^2) u v).const_mul
        (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4))
  simpa only [thetaWeightedGaussianIntegrand,
    thetaGaussian_right_derivative_multiplier] using h

/-- The derivative is the same as multiplying the derivative of the
plain Gaussian by the w-weight. This equality is useful for applying
the majorant from PR #24. -/
theorem thetaWeightedGaussian_right_deriv_eq_weighted
    (x p d0 u v w : ℝ) :
    deriv (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 u z w) v =
      Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        deriv (fun z : ℝ =>
          thetaGaussianModel (d0+w*x) (p+w*x^2) u z) v := by
  rw [(thetaWeightedGaussian_hasDerivAt_right x p d0 u v w).deriv]
  rw [(thetaGaussianModel_right_hasDerivAt
    (d0+w*x) (p+w*x^2) u v).deriv]
  ring

/-- The common integrable envelope from PR #24 bounds the true
derivative of the full w-integrand on the whole local parameter box. -/
theorem thetaWeightedGaussian_actual_deriv_uniform_envelope
    (x p d0 u v w : ℝ)
    (hp : 0 < p) (hw : 0 ≤ w)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (hxu : -(1:ℝ)/2 ≤ x*u)
    (hxv : -(1:ℝ)/2 ≤ x*v) :
    |deriv (fun z : ℝ =>
      thetaWeightedGaussianIntegrand x p d0 u z w) v| ≤
        ((|d0|+|p|)+w*(|x| *(1+|x|))) *
          (Real.exp (2*|d0|+|p|) *
            (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := by
  rw [thetaWeightedGaussian_right_deriv_eq_weighted]
  exact thetaGaussian_first_deriv_uniform_envelope
    x p d0 u v w hp hw hu hv hxu hxv

end W5
