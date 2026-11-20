import W5.ThetaSecondOrderPureJetCoefficient

/-!
# The true B02 certificate integral correction and second theta derivative

The numerical B02 polynomial is the coefficient d²/2 (not d²),
so the original integral correction in the certified theta
matrix must equal x²/(4·2!)=x²/8 times the genuine second
right derivative of the ENTIRE transformed theta Gaussian
series.

The proof does not assume termwise differentiation or Fubini:
they were already proved for all right-jet orders. We first
identify each original coefficient correction with its genuine
Lebesgue jet integral; then show summability and apply Fubini
and the all-orders second-derivative theorem.
-/

namespace W5
open MeasureTheory

/-- For each square index n the numerical (0,2) correction
is x²/8 times the true second-right Gaussian jet integral.
The factor 1/2! comes from B02=d²/2, not from an approximation. -/
theorem thetaCertificateCorrectionTerm_zero_two_eq_second_jet
    (x : ℝ) (n : ℕ) :
    thetaCertificateCorrectionTerm x (0:Fin 5) (2:Fin 5) n =
      (x^2/8) *
        (∫ w : ℝ, thetaHigherRightJetSeriesTerm 2 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateCorrectionTerm, thetaHigherRightJetSeriesTerm]
  · have hfunc :
        (fun w : ℝ => thetaHigherRightJetSeriesTerm 2 x 0 0 n w) =
        (fun w : ℝ =>
          let p : ℝ := (n:ℝ)^2
          let d0 : ℝ := (p-1)/x
          2 * (Real.exp (-(p-1)/x^2) *
            (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
              coefficientPolynomial (0:Fin 5) (2:Fin 5)
                (d0+w*x) (p+w*x^2)))) := by
      funext w
      simpa only [if_neg hn] using
        (thetaHigherRightJetSeriesTerm_two_zero_eq_B02 x n w)
    simp only [thetaCertificateCorrectionTerm, if_neg hn]
    rw [hfunc, MeasureTheory.integral_Ici_eq_integral_Ioi]
    simp only [integral_const_mul]
    ring

/-- The ORIGINAL numerical B02 integral correction series is
absolutely convergent for 0<x≤1, since it equals x²/8 times the
previously proved summable series of genuine integrated second
right Gaussian jets. -/
theorem thetaCertificateCorrectionTerm_zero_two_summable
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x (0:Fin 5) (2:Fin 5) n) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hjet : Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaHigherRightJetSeriesTerm 2 x 0 0 n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
    (thetaHigherRightJetSeries_integral_hasSum
      2 x 0 0 hx hx1 hz hz).summable
  have hfun :
      (fun n : ℕ =>
        thetaCertificateCorrectionTerm x (0:Fin 5) (2:Fin 5) n) =
      (fun n : ℕ =>
        (x^2/8) *
          (∫ w : ℝ, thetaHigherRightJetSeriesTerm 2 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
    funext n
    exact thetaCertificateCorrectionTerm_zero_two_eq_second_jet x n
  rw [hfun]
  exact hjet.mul_left (x^2/8)

/-- Full B02 numerical correction = x²/8 TIMES THE GENUINE
SECOND ORDINARY RIGHT DERIVATIVE of the entire transformed theta
Gaussian integrated infinite series at the Taylor origin. -/
theorem thetaCertificateCorrectionSeries_zero_two_eq_actual_second
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (∑' n : ℕ,
      thetaCertificateCorrectionTerm x (0:Fin 5) (2:Fin 5) n) =
      (x^2/8) *
        iteratedDeriv 2
          (fun y : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n y) 0 := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hFubini := (thetaHigherRightJetSeries_integral_hasSum
    2 x 0 0 hx hx1 hz hz).tsum_eq
  have hderiv := thetaGaussianIntegratedSeries_second_right_eq_integral_tsum
    x hx hx1
  have hsum :
      (∑' n : ℕ,
        ∫ w : ℝ,
          thetaHigherRightJetSeriesTerm 2 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) =
      iteratedDeriv 2
        (fun y : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n y) 0 :=
    hFubini.trans hderiv.symm
  calc
    (∑' n : ℕ,
      thetaCertificateCorrectionTerm x (0:Fin 5) (2:Fin 5) n) =
      (∑' n : ℕ,
        (x^2/8) *
          (∫ w : ℝ,
            thetaHigherRightJetSeriesTerm 2 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
      apply tsum_congr
      intro n
      exact thetaCertificateCorrectionTerm_zero_two_eq_second_jet x n
    _ = (x^2/8) * (∑' n : ℕ,
          ∫ w : ℝ,
            thetaHigherRightJetSeriesTerm 2 x 0 0 n w
              ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
      rw [tsum_mul_left]
    _ = _ := congrArg (fun z : ℝ => (x^2/8) * z) hsum

end W5
