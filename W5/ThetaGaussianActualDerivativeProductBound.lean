import W5.ThetaGaussianProductMajorant

/-!
# Domination of the actual first theta Gaussian derivative

The model majorant constructed earlier is now connected to the
genuine (weighted and differentiated) Gaussian theta summand.
The bound is uniform for |u|, |v| <= x/8, n >= 1 and w >= 0.
Its constant depends on x, not on n, u, v or w.

The n=0 summand is deliberately excluded: it is defined as zero in
the theta series and the formula p=n^2 would otherwise divide by zero.
This is an indexwise estimate, not yet a derivative/tsum exchange.
-/

namespace W5

/-- The affine derivative multiplier, times its quarter-root
upper bound, is controlled by a fixed polynomial in p and w
on the small theta parameter box. -/
theorem thetaGaussian_small_box_first_multiplier_polynomial
    (x p u w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hw : 0 ≤ w) (hu : |u| ≤ x/8) :
    (|((p-1)/x)+p*u| + w*|x*(1+x*u)|) *
        (1+w*x^2/p) ≤
      (1/x+2)*(p+1)*(w^2+w+1) := by
  have hp0 : 0 ≤ p := by linarith
  have hpPos : 0 < p := by linarith
  have hxinv : 0 ≤ 1/x := by positivity
  have hC : 0 ≤ 1/x+2 := by linarith
  have hdivpos : 0 ≤ (p-1)/x :=
    div_nonneg (by linarith) hx.le
  have hu1 : |u| ≤ 1 := hu.trans (by linarith)
  have hm := thetaGaussian_right_multiplier_uniform
    x p ((p-1)/x) u w hu1 hw
  have hm' :
      |((p-1)/x)+p*u| + w*|x*(1+x*u)| ≤
        ((p-1)/x+p)+w*(x*(1+x)) := by
    simpa only [abs_of_nonneg hdivpos,
      abs_of_nonneg hp0, abs_of_pos hx] using hm
  have hdivle : (p-1)/x ≤ p/x := by
    have heq : p/x-(p-1)/x = 1/x := by ring
    linarith
  have hxsq : x^2 ≤ x := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hxpoly : x*(1+x) ≤ 2 := by nlinarith [hxsq]
  have hwmul : w*(x*(1+x)) ≤ w*2 :=
    mul_le_mul_of_nonneg_left hxpoly hw
  have hwp : 0 ≤ w/x := div_nonneg hw hx.le
  have hupper :
      ((p-1)/x+p)+w*(x*(1+x)) ≤
        (1/x+2)*(p+w) := by
    calc
      ((p-1)/x+p)+w*(x*(1+x)) ≤
        p/x+p+2*w := by linarith [hdivle, hwmul]
      _ ≤ p/x+2*p+2*w+w/x := by linarith
      _ = (1/x+2)*(p+w) := by ring
  have hmul :
      |((p-1)/x)+p*u| + w*|x*(1+x*u)| ≤
        (1/x+2)*(p+w) := hm'.trans hupper
  have hx2 : x^2 ≤ 1 := by linarith [hxsq]
  have hfrac : x^2/p ≤ 1 :=
    (div_le_iff₀ hpPos).2 (by linarith)
  have hweight : 1+w*x^2/p ≤ 1+w := by
    have h := mul_le_mul_of_nonneg_left hfrac hw
    have heq : w*x^2/p = w*(x^2/p) := by ring
    rw [heq]
    nlinarith
  have hB : 0 ≤ 1+w*x^2/p := by positivity
  have hleft : 0 ≤ (1/x+2)*(p+w) :=
    mul_nonneg hC (add_nonneg hp0 hw)
  have hquad : (p+w)*(1+w) ≤ (p+1)*(w^2+w+1) := by
    have hsq : 0 ≤ p*w^2 := mul_nonneg hp0 (sq_nonneg w)
    nlinarith
  calc
    (|((p-1)/x)+p*u| + w*|x*(1+x*u)|) *
        (1+w*x^2/p) ≤
      ((1/x+2)*(p+w))*(1+w*x^2/p) :=
        mul_le_mul_of_nonneg_right hmul hB
    _ ≤ ((1/x+2)*(p+w))*(1+w) :=
        mul_le_mul_of_nonneg_left hweight hleft
    _ = (1/x+2)*((p+w)*(1+w)) := by ring
    _ ≤ (1/x+2)*((p+1)*(w^2+w+1)) :=
        mul_le_mul_of_nonneg_left hquad hC
    _ = (1/x+2)*(p+1)*(w^2+w+1) := by ring

/-- A genuine first-derivative domination theorem, including
the original outer theta Gaussian. Its right side has a
summable square-index factor and an integrable w-factor. -/
theorem thetaGaussian_small_box_first_deriv_product_bound
    (x p u v w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hw : 0 ≤ w) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    |Real.exp (-(p-1)/x^2) *
      (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        deriv (fun z : ℝ =>
          thetaGaussianModel ((p-1)/x+w*x) (p+w*x^2) u z) v)| ≤
      (Real.exp (3/4)*(1/x+2)) *
        ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
          ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w))) := by
  have hfirst :=
    thetaGaussian_small_box_first_deriv_decay x p u v w
      hx hx1 hp hw hu hv
  have hpoly :=
    thetaGaussian_small_box_first_multiplier_polynomial x p u w
      hx hx1 hp hw hu
  have hED : 0 ≤
      (Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p)) *
      Real.exp (-((1:ℝ)/4)*w) := by positivity
  calc
    |Real.exp (-(p-1)/x^2) *
      (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        deriv (fun z : ℝ =>
          thetaGaussianModel ((p-1)/x+w*x) (p+w*x^2) u z) v)| ≤
      (|((p-1)/x)+p*u|+w*|x*(1+x*u)|) *
        ((Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p)) *
          ((1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w))) := hfirst
    _ = ((|((p-1)/x)+p*u|+w*|x*(1+x*u)|) *
        (1+w*x^2/p)) *
        ((Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p)) *
          Real.exp (-((1:ℝ)/4)*w)) := by ring
    _ ≤ ((1/x+2)*(p+1)*(w^2+w+1)) *
        ((Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p)) *
          Real.exp (-((1:ℝ)/4)*w)) :=
        mul_le_mul_of_nonneg_right hpoly hED
    _ = (Real.exp (3/4)*(1/x+2)) *
        ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
          ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w))) := by ring

/-- For a genuine nonzero theta index n, the derivative is
bounded by one x-dependent constant times the summable
product majorant from PR #30. -/
theorem thetaGaussian_nonzero_index_first_deriv_le_product
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (u v w : ℝ) (hw : 0 ≤ w)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    |Real.exp (-((n:ℝ)^2-1)/x^2) *
      (Real.exp (-w) * (1+w*x^2/(n:ℝ)^2)^((1:ℝ)/4) *
        deriv (fun z : ℝ =>
          thetaGaussianModel (((n:ℝ)^2-1)/x+w*x)
            ((n:ℝ)^2+w*x^2) u z) v)| ≤
      (Real.exp (3/4)*(1/x+2)) *
        thetaGaussianProductMajorant n w := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith [sq_nonneg (n:ℝ)]
  have h := thetaGaussian_small_box_first_deriv_product_bound
    x (n:ℝ)^2 u v w hx hx1 hp hw hu hv
  simpa only [thetaGaussianProductMajorant] using h

end W5
