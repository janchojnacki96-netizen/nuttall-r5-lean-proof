import W5.ThetaGaussianWeightedMajorant

/-!
# First Gaussian derivative: an explicit integrable envelope

For fixed parameters and locally positive theta coordinates, the first
`v`-derivative of the transformed Gaussian has an affine multiplier in
`w`. Its weighted absolute value is bounded by a quadratic polynomial
times `exp (-w/4)`; that polynomial envelope is Lebesgue integrable on
`(0,∞)`.

This does not yet justify differentiating through the theta integral:
a *single* majorant uniform in a neighborhood and control of the outer
infinite square-index sum still have to be proved.
-/

namespace W5
open MeasureTheory

/-- The derivative's affine `w` multiplier is bounded by a positive
linear polynomial on the positive half-line. -/
theorem thetaGaussian_right_multiplier_abs_le
    (x p d0 u w : ℝ) (hw : 0 ≤ w) :
    |(-d0-p*u) - w*x*(1+x*u)| ≤
      |d0+p*u| + w * |x*(1+x*u)| := by
  calc
    |(-d0-p*u) - w*x*(1+x*u)| =
        |-(d0+p*u) - w*(x*(1+x*u))| := by
          congr 1
          ring
    _ ≤ |-(d0+p*u)| + |w*(x*(1+x*u))| :=
          abs_sub_le _ _
    _ = |d0+p*u| + w * |x*(1+x*u)| := by
          rw [abs_neg, abs_mul, abs_of_nonneg hw]

/-- On the local positivity patch the entire first differentiated,
quarter-root weighted theta Gaussian is bounded by a *quadratic*
polynomial/exponential envelope. -/
theorem thetaGaussian_weighted_right_deriv_abs_le
    (x p d0 u v w : ℝ)
    (hp : 0 < p) (hw : 0 ≤ w)
    (hu : -(1:ℝ)/2 ≤ x*u)
    (hv : -(1:ℝ)/2 ≤ x*v) :
    |Real.exp (-w) *
      (1+w*x^2/p)^((1:ℝ)/4) *
      deriv (fun z : ℝ =>
        thetaGaussianModel (d0+w*x) (p+w*x^2) u z) v| ≤
      (|d0+p*u| + w*|x*(1+x*u)|) *
        (Real.exp (-d0*(u+v)-p*u*v) *
          (1+w*x^2/p) * Real.exp (-((1:ℝ)/4)*w)) := by
  have hder :
      deriv (fun z : ℝ =>
        thetaGaussianModel (d0+w*x) (p+w*x^2) u z) v =
        ((-d0-p*u)-w*x*(1+x*u)) *
          thetaGaussianModel (d0+w*x) (p+w*x^2) u v := by
    rw [(thetaGaussianModel_right_hasDerivAt
      (d0+w*x) (p+w*x^2) u v).deriv]
    congr 1
    ring
  rw [hder]
  have hweighted :
      0 ≤ Real.exp (-w) *
        (1+w*x^2/p)^((1:ℝ)/4) *
        thetaGaussianModel (d0+w*x) (p+w*x^2) u v := by
    unfold thetaGaussianModel
    positivity
  have hmult := thetaGaussian_right_multiplier_abs_le x p d0 u w hw
  have hmult_nonneg :
      0 ≤ |d0+p*u| + w*|x*(1+x*u)| :=
    add_nonneg (abs_nonneg _) (mul_nonneg hw (abs_nonneg _))
  have hreshape :
      Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        (((-d0-p*u)-w*x*(1+x*u)) *
          thetaGaussianModel (d0+w*x) (p+w*x^2) u v) =
      ((-d0-p*u)-w*x*(1+x*u)) *
        (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          thetaGaussianModel (d0+w*x) (p+w*x^2) u v) := by
    ring
  rw [hreshape, abs_mul, abs_of_nonneg hweighted]
  exact (mul_le_mul_of_nonneg_right hmult hweighted).trans
    (mul_le_mul_of_nonneg_left
      (thetaGaussian_weighted_uniform_bound x p d0 u v w hp hw hu hv)
      hmult_nonneg)

/-- For arbitrary fixed parameters, the *explicit* differentiated
majorant is absolutely integrable on the unbounded positive `w` axis.
No interchange of derivative and integral is asserted. -/
theorem thetaGaussian_right_deriv_majorant_integrable
    (x p d0 u v : ℝ) :
    IntegrableOn
      (fun w : ℝ =>
        (|d0+p*u| + w*|x*(1+x*u)|) *
          (Real.exp (-d0*(u+v)-p*u*v) *
            (1+w*x^2/p) * Real.exp (-((1:ℝ)/4)*w)))
      (Set.Ioi (0:ℝ)) volume := by
  have h := (thetaGaussian_quadratic_exp_integrable
      (|x*(1+x*u)| * (x^2/p))
      (|d0+p*u| * (x^2/p) + |x*(1+x*u)|)
      (|d0+p*u|)).const_mul
        (Real.exp (-d0*(u+v)-p*u*v))
  convert h using 1
  funext w
  ring

end W5
