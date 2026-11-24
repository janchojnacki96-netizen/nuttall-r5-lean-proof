import W5.ThetaAllCoefficientPolynomialEnvelope
import W5.ThetaHigherJetSeparableEnvelope

/-!
# Uniform separability of ALL original theta B_ij coefficient polynomials

For 0<x≤1, p≥1 and w≥0 the *actual* arguments of the
original numerical certificate are
  d=(p-1)/x+w*x, q=p+w*x².

The previous theorem gives
  |B_ij(d,q)| ≤ C_ij (1+|d|+|q|)^8.

The EXISTING verified small-box theta multiplier inequality
(with u=0) controls |d|, and x²≤1 controls |q|.
The elementary inequality p+w+1≤(p+1)(w+1) then yields

  |B_ij((p-1)/x+wx,p+wx²)|
    ≤ C_ij (1/x+4)^8 (p+1)^8 (w+1)^8.

This is a SINGLE index/tail-separable estimate for ALL 25
original correction-polynomial factors. Its (p+1)^8 factor
can be absorbed by the already verified Gaussian square-index
decay; its (w+1)^8 factor by the already verified integrable
exponential tail. No differentiation or sum/integral exchange
is being assumed.
-/

namespace W5

/-- Concrete separated, eighth-degree certificate polynomial
bound that is UNIFORM over the positive w-half-line and every
square-index p≥1, for arbitrary i,j:Fin5. -/
theorem coefficientPolynomial_theta_arguments_separable
    (i j : Fin 5) (x p w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hp : 1 ≤ p) (hw : 0 ≤ w) :
    |coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2)| ≤
      thetaCoefficientAbsoluteWeight i j *
        ((1/x+4)^8 * (p+1)^8 * (w+1)^8) := by
  let C : ℝ := 1/x+2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC2 : 0 ≤ C+2 := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hpw : 0 ≤ p+w := add_nonneg hp0 hw
  have hsmall := thetaGaussian_small_box_right_multiplier_le
    x p (0:ℝ) w hx hx1 hp hw
    (by simp only [abs_zero]; positivity)
  have hsmall' :
      |(p-1)/x| + w*|x| ≤ C*(p+w) := by
    simpa only [mul_zero, add_zero, mul_one, C] using hsmall
  have hd :
      |(p-1)/x+w*x| ≤ C*(p+w) := by
    have ht := abs_add_le ((p-1)/x) (w*x)
    rw [abs_mul, abs_of_nonneg hw] at ht
    exact ht.trans hsmall'
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hq0 : 0 ≤ p+w*x^2 := by positivity
  have hq :
      |p+w*x^2| ≤ p+w := by
    rw [abs_of_nonneg hq0]
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hx2)]
  have hsep : p+w+1 ≤ (p+1)*(w+1) := by
    nlinarith [mul_nonneg hp0 hw]
  have hR :
      1+|(p-1)/x+w*x|+|p+w*x^2| ≤
        (C+2)*(p+1)*(w+1) := by
    have hfirst :
        1+|(p-1)/x+w*x|+|p+w*x^2| ≤
          1+(C+1)*(p+w) := by
      nlinarith [hd, hq]
    have hnext :
        1+(C+1)*(p+w) ≤ (C+2)*(p+w+1) := by
      have hpositive : 0 ≤ p+w+C+1 := by linarith
      nlinarith
    have hlast :
        (C+2)*(p+w+1) ≤ (C+2)*((p+1)*(w+1)) :=
      mul_le_mul_of_nonneg_left hsep hC2
    nlinarith [hfirst, hnext, hlast]
  have hpow :
      (1+|(p-1)/x+w*x|+|p+w*x^2|)^8 ≤
        ((C+2)*(p+1)*(w+1))^8 := by
    exact pow_le_pow_left₀ (by positivity) hR 8
  calc
    |coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2)| ≤
        thetaCoefficientAbsoluteWeight i j *
          (1+|(p-1)/x+w*x|+|p+w*x^2|)^8 :=
      coefficientPolynomial_abs_le_eighth_power i j _ _
    _ ≤ thetaCoefficientAbsoluteWeight i j *
          ((C+2)*(p+1)*(w+1))^8 :=
      mul_le_mul_of_nonneg_left hpow (thetaCoefficientAbsoluteWeight_nonneg i j)
    _ = thetaCoefficientAbsoluteWeight i j *
          ((1/x+4)^8 * (p+1)^8 * (w+1)^8) := by
      dsimp [C]
      ring

end W5
