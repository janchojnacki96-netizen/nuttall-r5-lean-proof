import W5.ThetaGaussianFirstDerivativeBound

/-!
# A common envelope for the first theta Gaussian derivative

The previous pointwise envelope depends on the two differentiation
coordinates. For |u|, |v| <= 1 we replace the affine multiplier and
the undamped exponential by constants depending only on x, p, d0.
This gives one integrable quadratic/exponential envelope on the local
patch x*u,x*v >= -1/2. Differentiation under the improper integral
and summation over square indices remain to be justified separately.
-/

namespace W5
open MeasureTheory

/-- An affine multiplier uniformly controlled on the unit u-ball. -/
theorem thetaGaussian_right_multiplier_uniform
    (x p d0 u w : ℝ) (hu : |u| ≤ 1) (hw : 0 ≤ w) :
    |d0+p*u| + w*|x*(1+x*u)| ≤
      (|d0|+|p|) + w*(|x| *(1+|x|)) := by
  have hpu : |p*u| ≤ |p| := by
    rw [abs_mul]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hu (abs_nonneg p))
  have hd : |d0+p*u| ≤ |d0| + |p| :=
    (abs_add_le d0 (p*u)).trans (add_le_add_left hpu _)
  have hxu : |x*u| ≤ |x| := by
    rw [abs_mul]
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hu (abs_nonneg x))
  have hxu1 : |1+x*u| ≤ 1+|x| := by
    calc
      |1+x*u| ≤ |(1:ℝ)| + |x*u| := abs_add_le _ _
      _ = 1+|x*u| := by norm_num
      _ ≤ 1+|x| := add_le_add_left hxu 1
  have hxbound : |x*(1+x*u)| ≤ |x| *(1+|x|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hxu1 (abs_nonneg x)
  have hprod := mul_le_mul_of_nonneg_left hxbound hw
  linarith

/-- The undamped Gaussian exponent is uniformly bounded above for
|u|,|v| <= 1, independently of the integration variable w. -/
theorem thetaGaussian_base_exponent_uniform
    (p d0 u v : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    Real.exp (-d0*(u+v)-p*u*v) ≤
      Real.exp (2*|d0|+|p|) := by
  have huv : |u+v| ≤ 2 := by
    calc
      |u+v| ≤ |u|+|v| := abs_add_le _ _
      _ ≤ 2 := by linarith
  have hpv : |u*v| ≤ 1 := by
    rw [abs_mul]
    calc
      |u| *|v| ≤ 1*|v| :=
        mul_le_mul_of_nonneg_right hu (abs_nonneg v)
      _ = |v| := one_mul _
      _ ≤ 1 := hv
  have hd : -d0*(u+v) ≤ 2*|d0| := by
    calc
      -d0*(u+v) = -(d0*(u+v)) := by ring
      _ ≤ |d0*(u+v)| := neg_le_abs _
      _ = |d0| *|u+v| := by rw [abs_mul]
      _ ≤ |d0| *2 :=
        mul_le_mul_of_nonneg_left huv (abs_nonneg d0)
      _ = 2*|d0| := by ring
  have hp : -p*u*v ≤ |p| := by
    calc
      -p*u*v = -(p*(u*v)) := by ring
      _ ≤ |p*(u*v)| := neg_le_abs _
      _ = |p| *|u*v| := by rw [abs_mul]
      _ ≤ |p| *1 :=
        mul_le_mul_of_nonneg_left hpv (abs_nonneg p)
      _ = |p| := mul_one _
  apply Real.exp_le_exp.mpr
  linarith

/-- One fixed Gaussian derivative majorant for the entire local
parameter box, with no u,v dependence on the right-hand side. -/
theorem thetaGaussian_first_deriv_uniform_envelope
    (x p d0 u v w : ℝ)
    (hp : 0 < p) (hw : 0 ≤ w)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (hxu : -(1:ℝ)/2 ≤ x*u)
    (hxv : -(1:ℝ)/2 ≤ x*v) :
    |Real.exp (-w) *
      (1+w*x^2/p)^((1:ℝ)/4) *
      deriv (fun z : ℝ =>
        thetaGaussianModel (d0+w*x) (p+w*x^2) u z) v| ≤
      ((|d0|+|p|)+w*(|x| *(1+|x|))) *
        (Real.exp (2*|d0|+|p|) *
          (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := by
  have hfirst :=
    thetaGaussian_weighted_right_deriv_abs_le x p d0 u v w hp hw hxu hxv
  have hm := thetaGaussian_right_multiplier_uniform x p d0 u w hu hw
  have he := thetaGaussian_base_exponent_uniform p d0 u v hu hv
  have hM : 0 ≤ (|d0|+|p|)+w*(|x| *(1+|x|)) := by positivity
  have hprod :
      (|d0+p*u|+w*|x*(1+x*u)|) *
        Real.exp (-d0*(u+v)-p*u*v) ≤
      ((|d0|+|p|)+w*(|x| *(1+|x|))) *
        Real.exp (2*|d0|+|p|) := by
    calc
      (|d0+p*u|+w*|x*(1+x*u)|) *
          Real.exp (-d0*(u+v)-p*u*v) ≤
        ((|d0|+|p|)+w*(|x| *(1+|x|))) *
          Real.exp (-d0*(u+v)-p*u*v) :=
            mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)
      _ ≤ ((|d0|+|p|)+w*(|x| *(1+|x|))) *
          Real.exp (2*|d0|+|p|) :=
            mul_le_mul_of_nonneg_left he hM
  have htail :
      0 ≤ (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w) := by
    positivity
  calc
    |Real.exp (-w) *
        (1+w*x^2/p)^((1:ℝ)/4) *
        deriv (fun z : ℝ =>
          thetaGaussianModel (d0+w*x) (p+w*x^2) u z) v| ≤
      (|d0+p*u|+w*|x*(1+x*u)|) *
        (Real.exp (-d0*(u+v)-p*u*v) *
          (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := hfirst
    _ = ((|d0+p*u|+w*|x*(1+x*u)|) *
          Real.exp (-d0*(u+v)-p*u*v)) *
          ((1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := by ring
    _ ≤ (((|d0|+|p|)+w*(|x| *(1+|x|))) *
          Real.exp (2*|d0|+|p|)) *
          ((1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) :=
            mul_le_mul_of_nonneg_right hprod htail
    _ = ((|d0|+|p|)+w*(|x| *(1+|x|))) *
        (Real.exp (2*|d0|+|p|) *
          (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := by ring

/-- The common parameter-independent-in-u,v envelope is absolutely
Lebesgue integrable over the positive integration half-line. -/
theorem thetaGaussian_first_deriv_uniform_envelope_integrable
    (x p d0 : ℝ) :
    IntegrableOn
      (fun w : ℝ =>
        ((|d0|+|p|)+w*(|x| *(1+|x|))) *
          (Real.exp (2*|d0|+|p|) *
            (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)))
      (Set.Ioi (0:ℝ)) volume := by
  have h := (thetaGaussian_quadratic_exp_integrable
      ((|x| *(1+|x|))*(x^2/p))
      ((|d0|+|p|)*(x^2/p)+|x| *(1+|x|))
      (|d0|+|p|)).const_mul
        (Real.exp (2*|d0|+|p|))
  have hfun :
      (fun w : ℝ =>
        ((|d0|+|p|)+w*(|x| *(1+|x|))) *
          (Real.exp (2*|d0|+|p|) *
            (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w))) =
      (fun w : ℝ =>
        Real.exp (2*|d0|+|p|) *
          (((|x| *(1+|x|))*(x^2/p)*w^2 +
            ((|d0|+|p|)*(x^2/p)+|x| *(1+|x|))*w +
            (|d0|+|p|)) * Real.exp (-((1:ℝ)/4)*w))) := by
    funext w
    ring
  rw [hfun]
  exact h

end W5
