import W5.ThetaAuditedCorrectionPointwise

/-!
# Quantitative bound for the ORIGINAL theta integral-correction summand

Unlike the previously proved separable Fubini bound, the estimate
here RETAINS the exact exp (-(n^2-1)/x^2) factor. The 25 original
coefficient polynomials are covered by one earlier proven bound,
and the w-integral is evaluated using the exact Mathlib Gamma moment.

For 0<x<=1 and n>=2, each correction summand is controlled by
  5*4096*16926797486 * (1/x^2)^4 *
     n^26 * exp (-(n^2-1)/x^2).
The remaining finite head and full infinite-tail comparisons can
therefore use the existing audited geometric majorant machinery.
-/

namespace W5
open MeasureTheory

/-- This bounds the TRUE original theta correction integrand,
not an unrelated auxiliary function. The exact Gaussian n-decay
survives intact; the residual w-dependence is integrable. -/
theorem thetaCertificateCorrectionIntegrand_norm_le_audited
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 2 ≤ n)
    (w : ℝ) (hw : 0 ≤ w) :
    ‖thetaCertificateCorrectionIntegrand x i j n w‖ ≤
      ((5*4096 : ℝ)*(1/x^2)^4 *
          thetaMajorantTerm (1/x^2) n) *
        ((w+1)^13 * Real.exp (-w)) := by
  have hn0 : n ≠ 0 := by omega
  let p : ℝ := (n:ℝ)^2
  have hnr : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : 1 ≤ p := by
    dsimp [p]
    nlinarith [sq_nonneg ((n:ℝ)-2)]
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hquarter : x^2/4 ≤ 1 := by nlinarith
  have hpow : (x^2/4)*p^12 ≤ p^13 := by
    calc
      (x^2/4)*p^12 ≤ 1*p^12 :=
        mul_le_mul_of_nonneg_right hquarter (by positivity)
      _ = p^12 := by ring
      _ ≤ p^13 := pow_le_pow_right₀ hp (by omega)
  have hpoly := thetaAuditedCoefficientPolynomial_shifted_abs_le
    x p w hx hx1 hp hw i j
  have hweight := thetaAuditedCorrectionQuarterPower_le
    x p w hx hx1 hp hw
  have hprod :
      (1+w*x^2/p)^((1:ℝ)/4) *
          |coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2)| ≤
        (w+1) *
          ((5*4096 : ℝ)*p^12*(1/x^2)^4*(w+1)^12) := by
    exact mul_le_mul hweight hpoly (abs_nonneg _) (by linarith)
  let E : ℝ := Real.exp (-(p-1)/x^2)
  have hnorm :
      ‖thetaCertificateCorrectionIntegrand x i j n w‖ =
        ((x^2/4)*E*Real.exp (-w)) *
          ((1+w*x^2/p)^((1:ℝ)/4) *
            |coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2)|) := by
    simp only [thetaCertificateCorrectionIntegrand, if_neg hn0]
    change ‖((x^2/4)*E) *
       (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2))‖ = _
    rw [Real.norm_eq_abs]
    simp only [abs_mul,
      abs_of_nonneg (show 0 ≤ x^2/4 by positivity),
      abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    ring
  have hfactor : 0 ≤ (x^2/4)*E*Real.exp (-w) := by
    dsimp [E]
    positivity
  have hbig : 0 ≤
      (5*4096 : ℝ)*(1/x^2)^4*E*((w+1)^13*Real.exp (-w)) := by
    dsimp [E]
    positivity
  calc
    ‖thetaCertificateCorrectionIntegrand x i j n w‖ =
        ((x^2/4)*E*Real.exp (-w)) *
          ((1+w*x^2/p)^((1:ℝ)/4) *
            |coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2)|) := hnorm
    _ ≤ ((x^2/4)*E*Real.exp (-w)) *
          ((w+1)*((5*4096 : ℝ)*p^12*(1/x^2)^4*(w+1)^12)) :=
      mul_le_mul_of_nonneg_left hprod hfactor
    _ = ((x^2/4)*p^12) *
          ((5*4096 : ℝ)*(1/x^2)^4*E*
            ((w+1)^13*Real.exp (-w))) := by ring
    _ ≤ p^13 *
          ((5*4096 : ℝ)*(1/x^2)^4*E*
            ((w+1)^13*Real.exp (-w))) :=
      mul_le_mul_of_nonneg_right hpow hbig
    _ = ((5*4096 : ℝ)*(1/x^2)^4 *
          thetaMajorantTerm (1/x^2) n) *
            ((w+1)^13*Real.exp (-w)) := by
      dsimp [p, E, thetaMajorantTerm]
      rw [show -((n:ℝ)^2-1)/x^2 =
        -(((n:ℝ)^2-1)*(1/x^2)) by ring]
      ring

/-- The ORIGINAL integrated correction is quantitatively dominated
by an integer multiple of the same audited n^26 Gaussian majorant.
All 25 coefficient entries have the SAME exact constant. -/
theorem thetaCertificateCorrectionTerm_abs_le_audited_majorant
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 2 ≤ n) :
    |thetaCertificateCorrectionTerm x i j n| ≤
      (5*4096*16926797486 : ℝ)*(1/x^2)^4 *
        thetaMajorantTerm (1/x^2) n := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let C : ℝ := (5*4096 : ℝ)*(1/x^2)^4 *
    thetaMajorantTerm (1/x^2) n
  have hC : 0 ≤ C := by
    dsimp [C, thetaMajorantTerm]
    positivity
  have hG : Integrable
      (fun w : ℝ => C*((w+1)^13*Real.exp (-w))) μ :=
    thetaAuditedCorrectionShiftedMoment_integrable.const_mul C
  have hpoint : ∀ᵐ w : ℝ ∂μ,
      ‖thetaCertificateCorrectionIntegrand x i j n w‖ ≤
        C*((w+1)^13*Real.exp (-w)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact thetaCertificateCorrectionIntegrand_norm_le_audited
      x hx hx1 i j n hn w hw.le
  have hmain :
      ‖∫ w : ℝ, thetaCertificateCorrectionIntegrand x i j n w ∂μ‖ ≤
        ∫ w : ℝ, C*((w+1)^13*Real.exp (-w)) ∂μ :=
    norm_integral_le_of_norm_le hG hpoint
  calc
    |thetaCertificateCorrectionTerm x i j n| =
        ‖∫ w : ℝ, thetaCertificateCorrectionIntegrand x i j n w ∂μ‖ := by
          simp only [thetaCertificateCorrectionTerm_eq_integral, Real.norm_eq_abs]
    _ ≤ ∫ w : ℝ, C*((w+1)^13*Real.exp (-w)) ∂μ := hmain
    _ = C*(16926797486 : ℝ) := by
      rw [integral_const_mul, thetaAuditedCorrectionShiftedMoment]
    _ = (5*4096*16926797486 : ℝ)*(1/x^2)^4 *
        thetaMajorantTerm (1/x^2) n := by
      dsimp [C]
      ring

end W5
