import W5.ThetaB11CorrectionEqualsMixedDerivative

/-!
# Absolutely summable elementary B00 theta certificate and exact splitting

The original independent numerical theta coefficient (0,0) is the
infinite series of a base Gaussian square-index term MINUS the
nonnegative-weight Lebesgue integral correction.

The preceding branch proved an exact indexwise decomposition but
deliberately did not assume that the two constituent infinite
series could be split. Here we *prove* the missing summability
for both, using:

* Mathlib's already formalized polynomial/Gaussian summability
  theorem with exponent coefficient 1/x²;
* the proven Fubini-integral summability of the original
  transformed Gaussian base series;
* the exact B00 certificate-to-integrated-series correspondence.

Only after these two Summable facts do we apply HasSum.sub
to obtain the genuine difference of two tsum expressions.

This is a coefficient-level identity and NOT an identification
of normalizedKernel with the theta certificate nor a sign theorem.
-/

namespace W5
open MeasureTheory

/-- The elementary n² exp(-(n²-1)/x²) square-index B00
certificate base contribution is summable for every x>0. -/
theorem thetaCertificateBaseTerm_zero_zero_summable
    (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ =>
      thetaCertificateBaseTerm x (0:Fin 5) (0:Fin 5) n) := by
  have hdecay : 0 < (1:ℝ)/x^2 := by positivity
  have hgauss : Summable (fun n : ℕ =>
      (n:ℝ)^2 * Real.exp (-((1:ℝ)/x^2)*(n:ℝ)^2)) :=
    theta_gaussian_polynomial_summable 2 ((1:ℝ)/x^2) hdecay
  have heq :
      (fun n : ℕ => thetaCertificateBaseTerm x (0:Fin 5) (0:Fin 5) n) =
      (fun n : ℕ =>
        Real.exp ((1:ℝ)/x^2) *
          ((n:ℝ)^2 * Real.exp (-((1:ℝ)/x^2)*(n:ℝ)^2))) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [thetaCertificateBaseTerm]
    · simp only [thetaCertificateBaseTerm, if_neg hn,
        coefficientPolynomial_zero_zero, mul_one]
      have hexp :
          Real.exp (-((n:ℝ)^2-1)/x^2) =
          Real.exp ((1:ℝ)/x^2) *
            Real.exp (-((1:ℝ)/x^2)*(n:ℝ)^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
  rw [heq]
  exact hgauss.mul_left (Real.exp ((1:ℝ)/x^2))

/-- The actual B00 correction series is separately summable
in the same domain where the full transformed theta integral
series has already been shown summable by Gaussian domination. -/
theorem thetaCertificateCorrectionTerm_zero_zero_summable
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x (0:Fin 5) (0:Fin 5) n) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hgauss := thetaHigherRightJetSeries_integrals_summable
    0 x 0 0 hx hx1 hz hz
  have heq :
      (fun n : ℕ => thetaGaussianIntegratedSeriesTerm x 0 n 0) =
      (fun n : ℕ =>
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
    funext n
    exact thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral x 0 0 n
  have hactual : Summable
      (fun n : ℕ => thetaGaussianIntegratedSeriesTerm x 0 n 0) := by
    rw [heq]
    exact hgauss
  have hcorr :
      (fun n : ℕ =>
        thetaCertificateCorrectionTerm x (0:Fin 5) (0:Fin 5) n) =
      (fun n : ℕ =>
        (x^2/4) * thetaGaussianIntegratedSeriesTerm x 0 n 0) := by
    funext n
    exact thetaCertificateCorrectionTerm_zero_zero_eq_integrated x n
  rw [hcorr]
  exact hactual.mul_left (x^2/4)

/-- For the first numerical theta coefficient, the infinitely many
original base-minus-correction terms can FINALLY be split into
two independent, separately convergent series; the integral
correction is identified with the true weighted theta series. -/
theorem thetaCoefficient_zero_zero_eq_base_minus_integrated
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaCoefficient x (0:Fin 5) (0:Fin 5) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (0:Fin 5) (0:Fin 5) n) -
      (x^2/4) *
        (∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n 0) := by
  have hb := thetaCertificateBaseTerm_zero_zero_summable x hx
  have hc := thetaCertificateCorrectionTerm_zero_zero_summable x hx hx1
  calc
    thetaCoefficient x (0:Fin 5) (0:Fin 5) =
        ∑' n : ℕ,
          (thetaCertificateBaseTerm x (0:Fin 5) (0:Fin 5) n -
            thetaCertificateCorrectionTerm x (0:Fin 5) (0:Fin 5) n) :=
      thetaCoefficient_eq_tsum_base_sub_correction x 0 0
    _ = (∑' n : ℕ,
          thetaCertificateBaseTerm x (0:Fin 5) (0:Fin 5) n) -
        (∑' n : ℕ,
          thetaCertificateCorrectionTerm x (0:Fin 5) (0:Fin 5) n) :=
      (hb.hasSum.sub hc.hasSum).tsum_eq
    _ = _ := by rw [thetaCertificateCorrectionSeries_zero_zero_eq_integrated]

end W5
