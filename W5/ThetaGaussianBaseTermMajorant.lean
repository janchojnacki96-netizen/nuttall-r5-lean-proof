import W5.ThetaGaussianSummableOpenPatch

/-!
# Gaussian domination of the original, undifferentiated theta terms

Mathlib's differentiation-of-series theorem needs the undifferentiated
series to converge at one basepoint in addition to the summably
dominated derivatives. This module derives a pointwise Gaussian bound
on the genuine *undifferentiated* weighted theta integrand, retaining
the exterior theta factor exp(-(p-1)/x²).

The parameter assumptions are precisely those of the small box used
for the first-derivative estimates. No series differentiation
claim or Nuttall r=5 determinant sign is made here.
-/

namespace W5

/-- The genuine weighted Gaussian integrand, including the original
outer square-index factor, is bounded by a polynomial-Gaussian
product uniformly on the shrinking parameter box. -/
theorem thetaGaussian_small_box_base_integrand_product_bound
    (x p u v w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hw : 0 ≤ w) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Real.exp (-(p-1)/x^2) *
      thetaWeightedGaussianIntegrand x p ((p-1)/x) u v w ≤
      Real.exp (3/4) *
        ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
          ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w))) := by
  have hpPos : 0 < p := by linarith
  obtain ⟨_, hxu⟩ :=
    thetaGaussian_small_box_inside_local_patch x u hx hx1 hu
  obtain ⟨_, hxv⟩ :=
    thetaGaussian_small_box_inside_local_patch x v hx hx1 hv
  have hweighted := thetaGaussian_weighted_uniform_bound
    x p ((p-1)/x) u v w hpPos hw hxu hxv
  have hdecay :=
    thetaGaussian_small_box_weighted_decay x p u v hx hx1 hp hu hv
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hfrac : x^2/p ≤ 1 :=
    (div_le_iff₀ hpPos).2 (by linarith)
  have hdivw : w*x^2/p ≤ w := by
    calc
      w*x^2/p = w*(x^2/p) := by ring
      _ ≤ w*1 := mul_le_mul_of_nonneg_left hfrac hw
      _ = w := by ring
  have hpoly : 0 ≤ w^2+w+1 := by positivity
  have hweight :
      1+w*x^2/p ≤ (p+1)*(w^2+w+1) := by
    have h1 : 1+w*x^2/p ≤ (w^2+w+1) := by
      nlinarith [hdivw, sq_nonneg w]
    have h2 : (w^2+w+1) ≤ (p+1)*(w^2+w+1) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ p) hpoly]
    exact h1.trans h2
  have hweight_nonneg : 0 ≤ 1+w*x^2/p := by
    have hterm : 0 ≤ w*x^2/p :=
      div_nonneg (mul_nonneg hw (sq_nonneg x)) hpPos.le
    linarith
  have hE : 0 ≤ Real.exp (3/4) *
      Real.exp (-((47:ℝ)/64)*p) *
      Real.exp (-((1:ℝ)/4)*w) := by positivity
  calc
    Real.exp (-(p-1)/x^2) *
        thetaWeightedGaussianIntegrand x p ((p-1)/x) u v w ≤
      Real.exp (-(p-1)/x^2) *
        (Real.exp (-((p-1)/x)*(u+v)-p*u*v) *
          (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := by
            unfold thetaWeightedGaussianIntegrand
            exact mul_le_mul_of_nonneg_left hweighted
              (Real.exp_nonneg _)
    _ = (Real.exp (-(p-1)/x^2) *
          Real.exp (-((p-1)/x)*(u+v)-p*u*v)) *
        ((1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := by ring
    _ ≤ (Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p)) *
        ((1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) :=
          mul_le_mul_of_nonneg_right hdecay
            (mul_nonneg hweight_nonneg (Real.exp_nonneg _))
    _ = (1+w*x^2/p) *
        (Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p) *
          Real.exp (-((1:ℝ)/4)*w)) := by ring
    _ ≤ ((p+1)*(w^2+w+1)) *
        (Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p) *
          Real.exp (-((1:ℝ)/4)*w)) :=
          mul_le_mul_of_nonneg_right hweight hE
    _ = Real.exp (3/4) *
        ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
          ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w))) := by ring

/-- In the actual theta series p=n², n>=1, the weighted
undifferentiated term is bounded by the product majorant
already known to be summable in n and integrable in w. -/
theorem thetaGaussian_nonzero_index_base_integrand_le_product
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (u v w : ℝ) (hw : 0 ≤ w)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Real.exp (-((n:ℝ)^2-1)/x^2) *
      thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) u v w ≤
      Real.exp (3/4) * thetaGaussianProductMajorant n w := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith [sq_nonneg (n:ℝ)]
  have h := thetaGaussian_small_box_base_integrand_product_bound
    x ((n:ℝ)^2) u v w hx hx1 hp hw hu hv
  simpa only [thetaGaussianProductMajorant] using h

end W5
