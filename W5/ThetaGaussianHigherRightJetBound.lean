import W5.ThetaWeightedGaussianHigherRightJets
import W5.ThetaGaussianBaseTermMajorant

/-!
# Polynomial-Gaussian majorants for arbitrary right theta jets

The affine v-multiplier is bounded by a linear expression in the
square-index p and in the integration variable w. Taking any fixed
power gives a polynomial loss without destroying the Gaussian decay.

We deliberately keep the polynomial (p+w)^k visible: the next task
is proving a summable/integrable separable envelope for each k, then
lifting higher derivatives through the w-integral and the n-series.
-/

namespace W5

/-- The true k-th weighted right Gaussian jet is bounded by the
k-th power of the first derivative's affine majorant. -/
theorem thetaWeightedGaussianRightJet_abs_le
    (k : ℕ) (x p d0 u v w : ℝ) (hw : 0 ≤ w) :
    |thetaWeightedGaussianRightJet k x p d0 u v w| ≤
      (|d0+p*u| + w*|x*(1+x*u)|)^k *
        |thetaWeightedGaussianIntegrand x p d0 u v w| := by
  have hm : |thetaWeightedGaussianRightMultiplier x p d0 u w| ≤
      |d0+p*u| + w*|x*(1+x*u)| := by
    simpa only [thetaWeightedGaussianRightMultiplier] using
      thetaGaussian_right_multiplier_abs_le x p d0 u w hw
  have hpow :=
    pow_le_pow_left₀
      (abs_nonneg (thetaWeightedGaussianRightMultiplier x p d0 u w)) hm k
  calc
    |thetaWeightedGaussianRightJet k x p d0 u v w| =
      |thetaWeightedGaussianRightMultiplier x p d0 u w|^k *
        |thetaWeightedGaussianIntegrand x p d0 u v w| := by
          simp only [thetaWeightedGaussianRightJet, abs_mul, abs_pow]
    _ ≤ (|d0+p*u| + w*|x*(1+x*u)|)^k *
          |thetaWeightedGaussianIntegrand x p d0 u v w| :=
            mul_le_mul_of_nonneg_right hpow (abs_nonneg _)

/-- The affine right-derivative multiplier has linear growth in p+w
uniformly for the small theta coordinate box. -/
theorem thetaGaussian_small_box_right_multiplier_le
    (x p u w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hw : 0 ≤ w) (hu : |u| ≤ x/8) :
    |((p-1)/x+p*u)| + w*|x*(1+x*u)| ≤
      (1/x+2)*(p+w) := by
  have hp0 : 0 ≤ p := by linarith
  have hd0 : 0 ≤ (p-1)/x :=
    div_nonneg (by linarith) hx.le
  have hu1 : |u| ≤ 1 := hu.trans (by linarith)
  have hm := thetaGaussian_right_multiplier_uniform
    x p ((p-1)/x) u w hu1 hw
  have hm' :
      |((p-1)/x+p*u)| + w*|x*(1+x*u)| ≤
        ((p-1)/x+p)+w*(x*(1+x)) := by
    simpa only [abs_of_nonneg hd0,
      abs_of_nonneg hp0, abs_of_pos hx] using hm
  have hdivle : (p-1)/x ≤ p/x := by
    have heq : p/x-(p-1)/x = 1/x := by ring
    have hxinv : 0 ≤ 1/x := by positivity
    linarith
  have hxsq : x^2 ≤ x := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hxpoly : x*(1+x) ≤ 2 := by
    nlinarith [hxsq]
  have hwmul : w*(x*(1+x)) ≤ w*2 :=
    mul_le_mul_of_nonneg_left hxpoly hw
  have hwp : 0 ≤ w/x := div_nonneg hw hx.le
  calc
    |((p-1)/x+p*u)| + w*|x*(1+x*u)| ≤
      ((p-1)/x+p)+w*(x*(1+x)) := hm'
    _ ≤ p/x+p+2*w := by linarith [hdivle, hwmul]
    _ ≤ p/x+2*p+2*w+w/x := by linarith
    _ = (1/x+2)*(p+w) := by ring

/-- A universal *pointwise* bound for any fixed right derivative
order of the genuine weighted Gaussian including the outer theta
damping. The surviving exponential decay in p is unchanged. -/
theorem thetaGaussian_small_box_higher_right_jet_bound
    (k : ℕ) (x p u v w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hw : 0 ≤ w) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Real.exp (-(p-1)/x^2) *
        |thetaWeightedGaussianRightJet k x p ((p-1)/x) u v w| ≤
      ((1/x+2)*(p+w))^k *
        (Real.exp (3/4) *
          ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
            ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w)))) := by
  have hpPos : 0 < p := by linarith
  have hE : 0 ≤ Real.exp (-(p-1)/x^2) := Real.exp_nonneg _
  have hbasepos : 0 ≤
      thetaWeightedGaussianIntegrand x p ((p-1)/x) u v w := by
    have hweight : 0 ≤ 1+w*x^2/p :=
      add_nonneg (by norm_num)
        (div_nonneg (mul_nonneg hw (sq_nonneg x)) hpPos.le)
    unfold thetaWeightedGaussianIntegrand thetaGaussianModel
    exact mul_nonneg
      (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hweight _))
      (Real.exp_nonneg _)
  have hjet := thetaWeightedGaussianRightJet_abs_le
    k x p ((p-1)/x) u v w hw
  have hm := thetaGaussian_small_box_right_multiplier_le
    x p u w hx hx1 hp hw hu
  have hmpow :=
    pow_le_pow_left₀
      (by positivity :
        0 ≤ |((p-1)/x+p*u)| + w*|x*(1+x*u)|) hm k
  have hbase := thetaGaussian_small_box_base_integrand_product_bound
    x p u v w hx hx1 hp hw hu hv
  have hmajorant : 0 ≤
      Real.exp (3/4) *
        ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
          ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w))) := by
    have hp1 : 0 ≤ p+1 := by linarith
    have hwpoly : 0 ≤ w^2+w+1 := by positivity
    positivity
  calc
    Real.exp (-(p-1)/x^2) *
        |thetaWeightedGaussianRightJet k x p ((p-1)/x) u v w| ≤
      Real.exp (-(p-1)/x^2) *
        ((|((p-1)/x+p*u)| + w*|x*(1+x*u)|)^k *
          |thetaWeightedGaussianIntegrand x p ((p-1)/x) u v w|) :=
            mul_le_mul_of_nonneg_left hjet hE
    _ = (|((p-1)/x+p*u)| + w*|x*(1+x*u)|)^k *
        (Real.exp (-(p-1)/x^2) *
          thetaWeightedGaussianIntegrand x p ((p-1)/x) u v w) := by
            rw [abs_of_nonneg hbasepos]
            ring
    _ ≤ (|((p-1)/x+p*u)| + w*|x*(1+x*u)|)^k *
        (Real.exp (3/4) *
          ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
            ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w)))) :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ ((1/x+2)*(p+w))^k *
        (Real.exp (3/4) *
          ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
            ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w)))) :=
          mul_le_mul_of_nonneg_right hmpow hmajorant

end W5
