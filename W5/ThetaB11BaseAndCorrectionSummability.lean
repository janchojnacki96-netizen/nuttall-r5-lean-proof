import W5.ThetaB00BaseSeriesSummability

/-!
# Independent summability and legitimate splitting of the B11 theta coefficient

The original square-index theta coefficient B11 contains the explicit
unintegrated polynomial d²-q and a weighted Gaussian integral
correction. Here both contributions are proved separately summable
under 0 < x ≤ 1, allowing an honest infinite-sum subtraction.

The base part is a polynomial combination of n², n⁴, n⁶ times
exp(-n²/x²), multiplied by exp(1/x²). We invoke the already
formalized Gaussian-polynomial summability theorem at orders
2,4,6; the correction uses the previously proved Fubini bounds
for genuine mixed (1,1) theta jets and the exact indexwise B11
certificate-to-integrated-jet identity.

The resulting exact formula expresses the numerical B11 coefficient
as an elementary Gaussian series minus x²/4 times the ACTUAL
mixed derivative of the infinite transformed Gaussian series.
No positivity/sign of a determinant or equality to the original
Nuttall normalized kernel is claimed.
-/

namespace W5
open MeasureTheory

/-- The elementary B11 certificate series is absolutely summable
for every x>0. Its polynomial is exactly
n² * (((n²-1)/x)² - n²), and hence a combination of
n², n⁴ and n⁶ times the surviving Gaussian exp(-n²/x²). -/
theorem thetaCertificateBaseTerm_one_one_summable
    (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ =>
      thetaCertificateBaseTerm x (1:Fin 5) (1:Fin 5) n) := by
  let c : ℝ := (1:ℝ)/x^2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have h2 : Summable (fun n : ℕ =>
      (n:ℝ)^2 * Real.exp (-c*(n:ℝ)^2)) :=
    theta_gaussian_polynomial_summable 2 c hc
  have h4 : Summable (fun n : ℕ =>
      (n:ℝ)^4 * Real.exp (-c*(n:ℝ)^2)) :=
    theta_gaussian_polynomial_summable 4 c hc
  have h6 : Summable (fun n : ℕ =>
      (n:ℝ)^6 * Real.exp (-c*(n:ℝ)^2)) :=
    theta_gaussian_polynomial_summable 6 c hc
  have hpoly : Summable (fun n : ℕ =>
      (c*(n:ℝ)^6 - (2*c+1)*(n:ℝ)^4 + c*(n:ℝ)^2) *
        Real.exp (-c*(n:ℝ)^2)) := by
    have heq :
        (fun n : ℕ =>
          (c*(n:ℝ)^6 - (2*c+1)*(n:ℝ)^4 + c*(n:ℝ)^2) *
            Real.exp (-c*(n:ℝ)^2)) =
        (fun n : ℕ =>
          c*((n:ℝ)^6 * Real.exp (-c*(n:ℝ)^2)) -
            (2*c+1)*((n:ℝ)^4 * Real.exp (-c*(n:ℝ)^2)) +
            c*((n:ℝ)^2 * Real.exp (-c*(n:ℝ)^2))) := by
      funext n
      ring
    rw [heq]
    exact ((h6.mul_left c).sub (h4.mul_left (2*c+1))).add
      (h2.mul_left c)
  have hfun :
      (fun n : ℕ => thetaCertificateBaseTerm x (1:Fin 5) (1:Fin 5) n) =
      (fun n : ℕ =>
        Real.exp c *
          ((c*(n:ℝ)^6 - (2*c+1)*(n:ℝ)^4 + c*(n:ℝ)^2) *
            Real.exp (-c*(n:ℝ)^2))) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [thetaCertificateBaseTerm]
    · simp only [thetaCertificateBaseTerm, if_neg hn,
        coefficientPolynomial_one_one]
      have hexp :
          Real.exp (-((n:ℝ)^2-1)/x^2) =
          Real.exp c * Real.exp (-c*(n:ℝ)^2) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [c]
        ring
      rw [hexp]
      rw [div_pow]
      dsimp [c]
      ring
  rw [hfun]
  exact hpoly.mul_left (Real.exp c)

/-- The original numerical B11 integral corrections form a
separately summable series for 0<x≤1, by exact identification
with the integrals of the genuine mixed Gaussian jets. -/
theorem thetaCertificateCorrectionTerm_one_one_summable
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x (1:Fin 5) (1:Fin 5) n) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hjet : Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
    (thetaMixedOneRightJetSeries_integral_hasSum
      1 x 0 0 hx hx1 hz hz).summable
  have hfun :
      (fun n : ℕ =>
        thetaCertificateCorrectionTerm x (1:Fin 5) (1:Fin 5) n) =
      (fun n : ℕ =>
        (x^2/4) *
          (∫ w : ℝ, thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
    funext n
    exact thetaCertificateCorrectionTerm_one_one_eq_mixed_integral x n
  rw [hfun]
  exact hjet.mul_left (x^2/4)

/-- The complete genuine B11 numerical theta coefficient is the
elementary square-index Gaussian B11 series MINUS (x²/4)
times the actual left-after-right (1,1) mixed derivative of
the transformed, infinite theta Gaussian integrated series.
In contrast to a formal decomposition, each separate tsum
is proved summable above. -/
theorem thetaCoefficient_one_one_eq_base_minus_actual_mixed_derivative
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaCoefficient x (1:Fin 5) (1:Fin 5) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (1:Fin 5) (1:Fin 5) n) -
      (x^2/4) *
        deriv (fun z : ℝ =>
          iteratedDeriv 1
            (fun y : ℝ =>
              ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 := by
  have hb := thetaCertificateBaseTerm_one_one_summable x hx
  have hc := thetaCertificateCorrectionTerm_one_one_summable x hx hx1
  calc
    thetaCoefficient x (1:Fin 5) (1:Fin 5) =
        ∑' n : ℕ,
          (thetaCertificateBaseTerm x (1:Fin 5) (1:Fin 5) n -
            thetaCertificateCorrectionTerm x (1:Fin 5) (1:Fin 5) n) :=
      thetaCoefficient_eq_tsum_base_sub_correction x 1 1
    _ = (∑' n : ℕ,
          thetaCertificateBaseTerm x (1:Fin 5) (1:Fin 5) n) -
        (∑' n : ℕ,
          thetaCertificateCorrectionTerm x (1:Fin 5) (1:Fin 5) n) :=
      (hb.hasSum.sub hc.hasSum).tsum_eq
    _ = _ := by
      rw [thetaCertificateCorrectionSeries_one_one_eq_actual_derivative
        x hx hx1]

end W5
