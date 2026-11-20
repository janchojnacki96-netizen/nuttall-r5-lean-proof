import W5.ThetaB02OriginalCorrectionEqualsSecondDerivative

/-!
# Summability and complete B02/B20 theta certificate coefficient splitting

The original coefficient B02(d,q)=B20(d,q)=d²/2 has an
unintegrated n² weighted Gaussian term and an integral correction.
The original coefficient definition combines these inside one
infinite series, so splitting this series is permissible only
after proving the two component series independently summable.

We prove the elementary B02 part summable from the n², n⁴, n⁶
Gaussian-polynomial summability theorems. The integral correction
is independently summable by the preceding real theta 2nd-jet
Fubini theorem. This yields exact full B02 and B20
coefficient identities involving true second derivatives of the
entire infinite transformed Gaussian theta series.

These are not yet identities for the original normalized
Nuttall kernel; no determinant sign is asserted here.
-/

namespace W5
open MeasureTheory

/-- The unintegrated B02 coefficient is an absolutely convergent
Gaussian square-index series for all x>0. -/
theorem thetaCertificateBaseTerm_zero_two_summable
    (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ =>
      thetaCertificateBaseTerm x (0:Fin 5) (2:Fin 5) n) := by
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
      ((c/2)*(n:ℝ)^6 - c*(n:ℝ)^4 + (c/2)*(n:ℝ)^2) *
        Real.exp (-c*(n:ℝ)^2)) := by
    have heq :
        (fun n : ℕ =>
          ((c/2)*(n:ℝ)^6 - c*(n:ℝ)^4 + (c/2)*(n:ℝ)^2) *
            Real.exp (-c*(n:ℝ)^2)) =
        (fun n : ℕ =>
          (c/2)*((n:ℝ)^6 * Real.exp (-c*(n:ℝ)^2)) -
            c*((n:ℝ)^4 * Real.exp (-c*(n:ℝ)^2)) +
            (c/2)*((n:ℝ)^2 * Real.exp (-c*(n:ℝ)^2))) := by
      funext n
      ring
    rw [heq]
    exact ((h6.mul_left (c/2)).sub (h4.mul_left c)).add
      (h2.mul_left (c/2))
  have hfun :
      (fun n : ℕ => thetaCertificateBaseTerm x (0:Fin 5) (2:Fin 5) n) =
      (fun n : ℕ =>
        Real.exp c *
          (((c/2)*(n:ℝ)^6 - c*(n:ℝ)^4 + (c/2)*(n:ℝ)^2) *
            Real.exp (-c*(n:ℝ)^2))) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [thetaCertificateBaseTerm]
    · simp only [thetaCertificateBaseTerm, if_neg hn,
        coefficientPolynomial_zero_two]
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

/-- The original B02 numerical coefficient equals the
separately summable elementary Gaussian square-index series
minus x²/8 times the actual second right derivative of
the full transformed theta series. -/
theorem thetaCoefficient_zero_two_eq_base_minus_actual_second_right
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaCoefficient x (0:Fin 5) (2:Fin 5) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (0:Fin 5) (2:Fin 5) n) -
      (x^2/8) *
        iteratedDeriv 2 (fun y : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n y) 0 := by
  have hb := thetaCertificateBaseTerm_zero_two_summable x hx
  have hc := thetaCertificateCorrectionTerm_zero_two_summable x hx hx1
  calc
    thetaCoefficient x (0:Fin 5) (2:Fin 5) =
        ∑' n : ℕ,
          (thetaCertificateBaseTerm x (0:Fin 5) (2:Fin 5) n -
            thetaCertificateCorrectionTerm x (0:Fin 5) (2:Fin 5) n) :=
      thetaCoefficient_eq_tsum_base_sub_correction x 0 2
    _ = (∑' n : ℕ,
          thetaCertificateBaseTerm x (0:Fin 5) (2:Fin 5) n) -
        (∑' n : ℕ,
          thetaCertificateCorrectionTerm x (0:Fin 5) (2:Fin 5) n) :=
      (hb.hasSum.sub hc.hasSum).tsum_eq
    _ = _ := by
      rw [thetaCertificateCorrectionSeries_zero_two_eq_actual_second
        x hx hx1]

/-- Symmetry of the elementary B20 and B02 Gaussian base summands. -/
theorem thetaCertificateBaseTerm_two_zero_eq_zero_two
    (x : ℝ) (n : ℕ) :
    thetaCertificateBaseTerm x (2:Fin 5) (0:Fin 5) n =
      thetaCertificateBaseTerm x (0:Fin 5) (2:Fin 5) n := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateBaseTerm]
  · simp only [thetaCertificateBaseTerm, if_neg hn]
    rw [coefficientPolynomial_symmetric (2:Fin 5) (0:Fin 5)]

/-- The actual second left and right derivatives of the
entire transformed theta integrated series agree at zero. -/
theorem thetaGaussianIntegratedSeries_second_left_eq_second_right
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    iteratedDeriv 2
      (fun y : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x y n 0) 0 =
    iteratedDeriv 2
      (fun y : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n y) 0 := by
  calc
    iteratedDeriv 2
        (fun y : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x y n 0) 0 =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaHigherRightJetSeriesTerm 2 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) :=
      thetaGaussianIntegratedSeries_second_left_eq_integral_tsum x hx hx1
    _ = _ := (thetaGaussianIntegratedSeries_second_right_eq_integral_tsum
      x hx hx1).symm

/-- The same complete B20 coefficient identity with the actual
second LEFT derivative of the infinite transformed theta series,
using exact symmetry in the Taylor parameters. -/
theorem thetaCoefficient_two_zero_eq_base_minus_actual_second_left
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaCoefficient x (2:Fin 5) (0:Fin 5) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (2:Fin 5) (0:Fin 5) n) -
      (x^2/8) *
        iteratedDeriv 2 (fun y : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x y n 0) 0 := by
  have hbase :
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (2:Fin 5) (0:Fin 5) n) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (0:Fin 5) (2:Fin 5) n) := by
    apply tsum_congr
    intro n
    exact thetaCertificateBaseTerm_two_zero_eq_zero_two x n
  calc
    thetaCoefficient x (2:Fin 5) (0:Fin 5) =
        thetaCoefficient x (0:Fin 5) (2:Fin 5) :=
      thetaCoefficient_symmetric x 2 0
    _ = (∑' n : ℕ,
          thetaCertificateBaseTerm x (0:Fin 5) (2:Fin 5) n) -
        (x^2/8) *
          iteratedDeriv 2 (fun y : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n y) 0 :=
      thetaCoefficient_zero_two_eq_base_minus_actual_second_right
        x hx hx1
    _ = _ := by rw [hbase, thetaGaussianIntegratedSeries_second_left_eq_second_right x hx hx1]

end W5
