import W5.ThetaHigherJetPolynomialTail

/-!
# Separating the index and integration variables in arbitrary right-jet bounds

For nonnegative p and w, the basic inequality

  p + w ≤ (p + 1) * (w + 1)

makes each fixed-degree loss (p+w)^k separable. Combining this
with the actual Gaussian jet estimate yields a product of an
index-polynomial Gaussian and a w-polynomial exponential.

The lemmas here are POINTWISE. The two factors have not yet been
assembled into a general dominated-differentiation theorem for
all higher jets; the higher-derivative under-integral and under-tsum
steps are separate obligations.
-/

namespace W5

/-- Polynomial growth in p+w separates into powers of p+1 and w+1
whenever both variables are nonnegative. -/
theorem thetaHigherJet_sum_pow_le_separable
    (k : ℕ) (p w : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w) :
    (p+w)^k ≤ ((p+1)*(w+1))^k := by
  have hpw : 0 ≤ p*w := mul_nonneg hp hw
  have hle : p+w ≤ (p+1)*(w+1) := by
    nlinarith
  exact pow_le_pow_left₀ (add_nonneg hp hw) hle k

/-- The affine v-multiplier has a separable k-th power
uniformly on the shrinking theta parameter box. -/
theorem thetaGaussian_small_box_right_multiplier_separable
    (k : ℕ) (x p u w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hw : 0 ≤ w) (hu : |u| ≤ x/8) :
    (|((p-1)/x+p*u)| + w*|x*(1+x*u)|)^k ≤
      ((1/x+2)*(p+1)*(w+1))^k := by
  have hp0 : 0 ≤ p := by linarith
  have hC : 0 ≤ 1/x+2 := by positivity
  have hm := thetaGaussian_small_box_right_multiplier_le
    x p u w hx hx1 hp hw hu
  have hsep := thetaHigherJet_sum_pow_le_separable
    k p w hp0 hw
  have hpre : (1/x+2)*(p+w) ≤
      (1/x+2)*((p+1)*(w+1)) :=
    mul_le_mul_of_nonneg_left
      (by
        have hle : p+w ≤ (p+1)*(w+1) := by
          nlinarith [mul_nonneg hp0 hw]
        exact hle) hC
  calc
    (|((p-1)/x+p*u)| + w*|x*(1+x*u)|)^k ≤
      ((1/x+2)*(p+w))^k :=
        pow_le_pow_left₀ (by positivity) hm k
    _ ≤ ((1/x+2)*((p+1)*(w+1)))^k :=
        pow_le_pow_left₀
          (mul_nonneg hC (add_nonneg hp0 hw)) hpre k
    _ = ((1/x+2)*(p+1)*(w+1))^k := by ring

/-- A genuine, arbitrary-degree right-jet majorant that completely
separates p and w. This is the natural form to feed into a
summable-in-n and integrable-in-w domination theorem. -/
theorem thetaGaussian_small_box_higher_right_jet_separable_bound
    (k : ℕ) (x p u v w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hw : 0 ≤ w) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Real.exp (-(p-1)/x^2) *
        |thetaWeightedGaussianRightJet k x p ((p-1)/x) u v w| ≤
      ((1/x+2)^k * Real.exp (3/4)) *
        (((p+1)^(k+1) * Real.exp (-((47:ℝ)/64)*p)) *
          (((w+1)^k*(w^2+w+1)) * Real.exp (-((1:ℝ)/4)*w))) := by
  have hp0 : 0 ≤ p := by linarith
  have hC : 0 ≤ 1/x+2 := by positivity
  have hindex : 0 ≤ p+1 := by linarith
  have htail : 0 ≤ w^2+w+1 := by positivity
  have hM : 0 ≤
      Real.exp (3/4) *
        ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
          ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w))) := by positivity
  have hsep : (p+w)^k ≤ ((p+1)*(w+1))^k :=
    thetaHigherJet_sum_pow_le_separable k p w hp0 hw
  have hpre : (1/x+2)*(p+w) ≤
      (1/x+2)*((p+1)*(w+1)) := by
    apply mul_le_mul_of_nonneg_left _ hC
    nlinarith [mul_nonneg hp0 hw]
  have hpow : ((1/x+2)*(p+w))^k ≤
      ((1/x+2)*((p+1)*(w+1)))^k :=
    pow_le_pow_left₀ (mul_nonneg hC (add_nonneg hp0 hw)) hpre k
  have h := thetaGaussian_small_box_higher_right_jet_bound
    k x p u v w hx hx1 hp hw hu hv
  calc
    Real.exp (-(p-1)/x^2) *
        |thetaWeightedGaussianRightJet k x p ((p-1)/x) u v w| ≤
      ((1/x+2)*(p+w))^k *
        (Real.exp (3/4) *
          ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
            ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w)))) := h
    _ ≤ ((1/x+2)*((p+1)*(w+1)))^k *
        (Real.exp (3/4) *
          ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
            ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w)))) :=
        mul_le_mul_of_nonneg_right hpow hM
    _ = ((1/x+2)^k * Real.exp (3/4)) *
        (((p+1)^(k+1) * Real.exp (-((47:ℝ)/64)*p)) *
          (((w+1)^k*(w^2+w+1)) * Real.exp (-((1:ℝ)/4)*w))) := by
            simp only [mul_pow, pow_succ]
            ring

end W5
