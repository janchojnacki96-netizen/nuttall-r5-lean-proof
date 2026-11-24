import W5.ThetaGaussianIntegralCoefficient

/-!
# Uniform exponential decay of the transformed theta Gaussian integrand

A direct factorization of the `w`-dependent Gaussian exponent gives
  exp(-w) exp(-(d0+w*x)*(u+v) - (p+w*x²)*u*v)
  = exp(-d0*(u+v)-p*u*v) exp(-w*(1+x*u)*(1+x*v)).

For local parameters with `x*u >= -1/2` and `x*v >= -1/2`,
the last exponential is bounded above by `exp(-w/4)` on `w >= 0`.
This is the crucial Gaussian damping for a future dominated
differentiation-under-integral theorem.

The results below are unconditional pointwise identities and
inequalities. Uniform bounds for all differentiated integrands and
the required integration/summation exchange are still open.
-/

namespace W5

theorem thetaGaussian_exponent_split
    (x p d0 u v w : ℝ) :
    -w - (d0+w*x)*(u+v) - (p+w*x^2)*u*v =
      -d0*(u+v) - p*u*v - w*(1+x*u)*(1+x*v) := by
  ring

/-- An exact Gaussian/exponential factorization, without any
positivity, approximation, or convergence hypothesis. -/
theorem thetaGaussian_weight_factor
    (x p d0 u v w : ℝ) :
    Real.exp (-w) * thetaGaussianModel (d0+w*x) (p+w*x^2) u v =
      Real.exp (-d0*(u+v)-p*u*v) *
        Real.exp (-w*(1+x*u)*(1+x*v)) := by
  unfold thetaGaussianModel
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The coefficient of w in the Gaussian decay stays uniformly
above one quarter in a fixed local neighborhood of u=v=0. -/
theorem thetaGaussian_decay_quarter
    (x u v : ℝ)
    (hu : -(1:ℝ)/2 ≤ x*u)
    (hv : -(1:ℝ)/2 ≤ x*v) :
    (1:ℝ)/4 ≤ (1+x*u)*(1+x*v) := by
  have hu' : (1:ℝ)/2 ≤ 1+x*u := by linarith
  have hv' : (1:ℝ)/2 ≤ 1+x*v := by linarith
  have hm := mul_le_mul hu' hv' (by norm_num : (0:ℝ) ≤ 1/2)
    (by linarith : (0:ℝ) ≤ 1+x*u)
  nlinarith

/-- A locally uniform integrable exponential envelope for the
unweighted Gaussian w-damping. -/
theorem thetaGaussian_uniform_decay
    (x u v w : ℝ)
    (hu : -(1:ℝ)/2 ≤ x*u)
    (hv : -(1:ℝ)/2 ≤ x*v)
    (hw : 0 ≤ w) :
    Real.exp (-w*(1+x*u)*(1+x*v)) ≤ Real.exp (-w/4) := by
  have hq := thetaGaussian_decay_quarter x u v hu hv
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ w * ((1+x*u)*(1+x*v) - (1:ℝ)/4) :=
    mul_nonneg hw (by linarith)
  nlinarith

end W5
