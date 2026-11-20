import W5.ThetaCertificateBaseCorrectionSplit

/-!
# The actual theta certificate B00 correction IS the genuine integrated Gaussian series

The original coefficient formula uses an improper Lebesgue integral
over [0,∞) and the numerical B00 polynomial. The transformed Gaussian
series uses a Lebesgue integral over (0,∞) and the actual weighted
Gaussian. By exact B00=1, Gaussian zero-parameter normalization,
and the already proved equality of the two integral conventions,
these integrals coincide at every square index.

Consequently the *entire sum* of the original B00 integral corrections
is exactly x²/4 times the genuine transformed Gaussian series at
the Taylor origin, with no unproved exchange of derivatives/integrals
or sum/integral terms.

This settles the correction part of B00 but does not identify
the remaining elementary n²-weighted component or the original
normalized Nuttall kernel.
-/

namespace W5
open MeasureTheory

/-- The original B00 certificate integrand equals the
actual weighted Gaussian at u=v=0, for all real parameters. -/
theorem thetaCertificate_B00_integrand_eq_weightedGaussian
    (x p d0 w : ℝ) :
    Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        coefficientPolynomial (0:Fin 5) (0:Fin 5)
          (d0+w*x) (p+w*x^2) =
      thetaWeightedGaussianIntegrand x p d0 0 0 w := by
  rw [coefficientPolynomial_zero_zero]
  simp only [mul_one]
  unfold thetaWeightedGaussianIntegrand
  rw [thetaGaussianModel_zero_zero]
  ring

/-- The exact B00 integral in the ORIGINAL certificate is the
same Lebesgue integral as the genuine Gaussian model at the
Taylor origin; {0} has measure zero, so Ici and Ioi agree. -/
theorem thetaCertificate_B00_integral_eq_weightedGaussian
    (x p d0 : ℝ) :
    (∫ w in Set.Ici (0:ℝ),
      Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        coefficientPolynomial (0:Fin 5) (0:Fin 5)
          (d0+w*x) (p+w*x^2) ∂volume) =
      ∫ w : ℝ, thetaWeightedGaussianIntegrand x p d0 0 0 w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  apply integral_congr_ae
  filter_upwards [] with w
  exact thetaCertificate_B00_integrand_eq_weightedGaussian x p d0 w

/-- Every n-th *actual original* theta B00 integral correction
is precisely x²/4 times the original transformed Gaussian
integrated-series term at u=v=0, including n=0. -/
theorem thetaCertificateCorrectionTerm_zero_zero_eq_integrated
    (x : ℝ) (n : ℕ) :
    thetaCertificateCorrectionTerm x (0:Fin 5) (0:Fin 5) n =
      (x^2/4) * thetaGaussianIntegratedSeriesTerm x 0 n 0 := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateCorrectionTerm, thetaGaussianIntegratedSeriesTerm]
  · simp only [thetaCertificateCorrectionTerm,
      thetaGaussianIntegratedSeriesTerm, if_neg hn]
    rw [thetaCertificate_B00_integral_eq_weightedGaussian
      x ((n:ℝ)^2) (((n:ℝ)^2-1)/x)]
    ring

/-- The complete infinite sum of B00 corrections equals a
single scalar multiple of the genuine transformed Gaussian series.
No separate sum-of-differences interchange is involved. -/
theorem thetaCertificateCorrectionSeries_zero_zero_eq_integrated
    (x : ℝ) :
    (∑' n : ℕ, thetaCertificateCorrectionTerm x
      (0:Fin 5) (0:Fin 5) n) =
      (x^2/4) *
        (∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n 0) := by
  simp_rw [thetaCertificateCorrectionTerm_zero_zero_eq_integrated]
  rw [tsum_mul_left]

end W5
