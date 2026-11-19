import W5.ThetaGaussianPolynomialIntegrability

/-!
# Integrable domination of the weighted theta Gaussian model

The theta coefficient integral also contains the quarter-power
(1+w*x²/p)^(1/4), in addition to the Gaussian factor.
For p>0 and w>=0, the quarter power is bounded by its base.
The combined Gaussian/weight is therefore bounded pointwise by an
explicit integrable affine-polynomial multiple of exp(-w/4), locally
uniformly in u,v near zero.

This controls the *undifferentiated* theta integrand. Higher
derivative integrands and the infinite square-index sum still
require separate proofs before any differentiation-under-integral
claim can be made.
-/

namespace W5
open MeasureTheory

/-- A nonnegative quarter power grows no faster than the linear
base on the positive half-line. -/
theorem theta_quarter_root_le_linear
    (c w : ℝ) (hc : 0 ≤ c) (hw : 0 ≤ w) :
    (1+c*w)^((1:ℝ)/4) ≤ 1+c*w := by
  have hb : (1:ℝ) ≤ 1+c*w := by
    have hcw : 0 ≤ c*w := mul_nonneg hc hw
    linarith
  have h := Real.rpow_le_rpow_of_exponent_le
    hb (show ((1:ℝ)/4) ≤ 1 by norm_num)
  simpa only [Real.rpow_one] using h

/-- Positive-base condition for the original fractional theta weight. -/
private theorem theta_weight_base_pos (x p w : ℝ)
    (hp : 0 < p) (hw : 0 ≤ w) :
    0 < 1+w*x^2/p := by
  have hx : 0 ≤ x^2 := sq_nonneg x
  have hterm : 0 ≤ w*x^2/p :=
    div_nonneg (mul_nonneg hw hx) (le_of_lt hp)
  linarith

/-- The complete undifferentiated Gaussian factor, including its
quarter-root weight, has an explicit exp(-w/4) local majorant.
The envelope on the right is independent of w except for an affine
polynomial and the decaying exponential. -/
theorem thetaGaussian_weighted_uniform_bound
    (x p d0 u v w : ℝ)
    (hp : 0 < p) (hw : 0 ≤ w)
    (hu : -(1:ℝ)/2 ≤ x*u)
    (hv : -(1:ℝ)/2 ≤ x*v) :
    Real.exp (-w) *
        (1+w*x^2/p)^((1:ℝ)/4) *
        thetaGaussianModel (d0+w*x) (p+w*x^2) u v ≤
      Real.exp (-d0*(u+v)-p*u*v) *
        (1+w*x^2/p) * Real.exp (-((1:ℝ)/4)*w) := by
  have hweight : 0 ≤ (1+w*x^2/p)^((1:ℝ)/4) :=
    (Real.rpow_pos_of_pos (theta_weight_base_pos x p w hp hw) _).le
  have hc : 0 ≤ x^2/p :=
    div_nonneg (sq_nonneg x) (le_of_lt hp)
  have hrewrite : 1+w*x^2/p = 1+(x^2/p)*w := by ring
  have hweight_le :
      (1+w*x^2/p)^((1:ℝ)/4) ≤ 1+w*x^2/p := by
    rw [hrewrite]
    exact theta_quarter_root_le_linear (x^2/p) w hc hw
  have hexp := thetaGaussian_uniform_decay x u v w hu hv hw
  have hprod :
      Real.exp (-w*(1+x*u)*(1+x*v)) *
        (1+w*x^2/p)^((1:ℝ)/4) ≤
      Real.exp (-((1:ℝ)/4)*w) * (1+w*x^2/p) := by
    apply le_trans
      (mul_le_mul_of_nonneg_right hexp hweight)
    exact mul_le_mul_of_nonneg_left hweight_le (Real.exp_nonneg _)
  calc
    Real.exp (-w) *
        (1+w*x^2/p)^((1:ℝ)/4) *
        thetaGaussianModel (d0+w*x) (p+w*x^2) u v =
      (Real.exp (-w) *
        thetaGaussianModel (d0+w*x) (p+w*x^2) u v) *
          (1+w*x^2/p)^((1:ℝ)/4) := by ring
    _ = Real.exp (-d0*(u+v)-p*u*v) *
        (Real.exp (-w*(1+x*u)*(1+x*v)) *
          (1+w*x^2/p)^((1:ℝ)/4)) := by
      rw [thetaGaussian_weight_factor]
      ring
    _ ≤ Real.exp (-d0*(u+v)-p*u*v) *
        (Real.exp (-((1:ℝ)/4)*w) * (1+w*x^2/p)) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
    _ = Real.exp (-d0*(u+v)-p*u*v) *
        (1+w*x^2/p) * Real.exp (-((1:ℝ)/4)*w) := by ring

/-- The explicit right-hand side above is absolutely integrable
over the unbounded positive w half-line. -/
theorem thetaGaussian_weighted_majorant_integrable
    (x p d0 u v : ℝ) :
    IntegrableOn
      (fun w : ℝ =>
        Real.exp (-d0*(u+v)-p*u*v) *
          (1+w*x^2/p) * Real.exp (-((1:ℝ)/4)*w))
      (Set.Ioi (0:ℝ)) volume := by
  have h := (thetaGaussian_quadratic_exp_integrable
    (0:ℝ) (x^2/p) 1).const_mul
      (Real.exp (-d0*(u+v)-p*u*v))
  convert h using 1
  funext w
  ring

end W5
