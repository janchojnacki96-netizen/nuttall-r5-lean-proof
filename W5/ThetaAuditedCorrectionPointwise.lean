import W5.ThetaAuditedCorrectionMoment
import W5.ThetaAuditedBaseTermMajorant

/-!
# Pointwise bounds for the ORIGINAL theta integral-correction factors

This file retains the real Gaussian exponent while bounding the
actual shifted coefficient polynomial at
  d=(p-1)/x+w*x, q=p+w*x^2.
It reuses the pre-existing exact all-25 polynomial bound; no
enumeration of the 25 coefficients or approximation is repeated.

For 0<x<=1, p>=1 and w>=0:
  |B_ij(d,q)| <= 5*4096*p^12*(1/x^2)^4*(1+w)^12,
and the original quarter-power weight is <= 1+w.

The combined degree-13 moment is computed in the imported Gamma
module. Connecting the integral of the product to the original
correction term is a separate step.
-/

namespace W5

/-- A uniform, shifted version of the already-certified
all-25 polynomial estimate, keeping the sharp 4096 constant
of the original finite audit. -/
theorem thetaAuditedCoefficientPolynomial_shifted_abs_le
    (x p w : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hp : 1 ≤ p) (hw : 0 ≤ w) (i j : Fin 5) :
    |coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2)| ≤
      (5*4096 : ℝ)*p^12*(1/x^2)^4*(w+1)^12 := by
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hp0 : 0 ≤ p := by linarith
  have hpx : 0 ≤ p-1 := by linarith
  have hdp : 0 ≤ (p-1)/x+w*x :=
    add_nonneg (div_nonneg hpx hx.le) (mul_nonneg hw hx.le)
  have hqp : 0 ≤ p+w*x^2 := by positivity
  have hwx : w*x^2 ≤ w := by
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left hx2 hw)
  have hpw : w ≤ p*w := by
    nlinarith [mul_nonneg hpx hw]
  have hpre : (1+(p-1)/x+w*x)*x ≤ 2*p*(w+1) := by
    calc
      (1+(p-1)/x+w*x)*x = x+(p-1)+w*x^2 := by
        field_simp [ne_of_gt hx] <;> ring
      _ ≤ p+w := by linarith
      _ ≤ 2*p*(w+1) := by
        nlinarith [hpw, mul_nonneg hp0 hw]
  have hD : 1+((p-1)/x+w*x) ≤ (2*p/x)*(w+1) := by
    calc
      1+((p-1)/x+w*x) = 1+(p-1)/x+w*x := by ring
      _ ≤ 2*p*(w+1)/x := (le_div_iff₀ hx).mpr hpre
      _ = (2*p/x)*(w+1) := by ring
  have hQ : 1+(p+w*x^2) ≤ (2*p)*(w+1) := by
    nlinarith [hwx, hpw, mul_nonneg hp0 hw]
  have h8 : (1+((p-1)/x+w*x))^8 ≤
      ((2*p/x)*(w+1))^8 :=
    pow_le_pow_left₀ (by positivity) hD 8
  have h4 : (1+(p+w*x^2))^4 ≤
      ((2*p)*(w+1))^4 :=
    pow_le_pow_left₀ (by positivity) hQ 4
  calc
    |coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2)| ≤
        (5:ℝ)*(1+((p-1)/x+w*x))^8*(1+(p+w*x^2))^4 :=
      coefficientPolynomial_abs_bound i j _ _ hdp hqp
    _ ≤ (5:ℝ)*((2*p/x)*(w+1))^8*(1+(p+w*x^2))^4 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h8 (by norm_num))
        (by positivity)
    _ ≤ (5:ℝ)*((2*p/x)*(w+1))^8*((2*p)*(w+1))^4 :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (5*4096:ℝ)*p^12*(1/x^2)^4*(w+1)^12 := by
      field_simp [ne_of_gt hx] <;> ring

/-- The genuine quarter-power factor in the original theta
correction has an elementary linear majorant. -/
theorem thetaAuditedCorrectionQuarterPower_le
    (x p w : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hp : 1 ≤ p) (hw : 0 ≤ w) :
    (1+w*x^2/p)^((1:ℝ)/4) ≤ w+1 := by
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hp0 : 0 < p := by linarith
  have hbase : 1 ≤ 1+w*x^2/p := by
    have : 0 ≤ w*x^2/p := div_nonneg (mul_nonneg hw (sq_nonneg x)) hp0.le
    linarith
  have hratio : w*x^2/p ≤ w := by
    apply (div_le_iff₀ hp0).mpr
    have ha : w*x^2 ≤ w := by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hx2 hw)
    have hb : w ≤ w*p := by nlinarith [mul_nonneg hw (by linarith : 0 ≤ p-1)]
    linarith
  calc
    (1+w*x^2/p)^((1:ℝ)/4) ≤ 1+w*x^2/p :=
      Real.rpow_le_self_of_one_le hbase (by norm_num)
    _ ≤ w+1 := by linarith

end W5
