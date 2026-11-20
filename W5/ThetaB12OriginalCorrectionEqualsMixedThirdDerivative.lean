import W5.ThetaMixedOneTwoGenuineSeriesJet

/-!
# Original B12 correction = x²/8 times a genuine mixed third derivative

The (1,2) numerical theta coefficient is a TAYLOR coefficient,
so B12(d,q)=(-d³+2dq)/2 and its numerical integral correction
carries the factorial 1/2! relative to the actual derivative.

The exact pointwise B12 jet correspondence was established in
the previous module. Here we identify the ORIGINAL numerical
theta correction with x²/8 times the genuine weighted mixed
Gaussian jet integral for every square index n, prove the
correction series separately summable, and replace its full
sum by x²/8 times the TRUE (one-left, two-right) mixed
derivative of the entire transformed Gaussian theta series.

All differentiated infinite-series and Lebesgue integral
interchanges are already justified by the common-parameter
patch estimates. This does not identify the elementary
unintegrated B12 coefficient or the original normalized
Nuttall kernel. No sign conclusion is asserted.
-/

namespace W5
open MeasureTheory

/-- The original index-n B12 certificate integral correction
is exactly x²/8 times the weighted actual (1,2) Gaussian jet
integral; n=0 is treated directly. -/
theorem thetaCertificateCorrectionTerm_one_two_eq_mixed_jet
    (x : ℝ) (n : ℕ) :
    thetaCertificateCorrectionTerm x (1:Fin 5) (2:Fin 5) n =
      (x^2/8) *
        (∫ w : ℝ,
          thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateCorrectionTerm, thetaMixedOneRightJetSeriesTerm]
  · have hfunc :
        (fun w : ℝ => thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w) =
        (fun w : ℝ =>
          let p : ℝ := (n:ℝ)^2
          let d0 : ℝ := (p-1)/x
          2 * (Real.exp (-(p-1)/x^2) *
            (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
              coefficientPolynomial (1:Fin 5) (2:Fin 5)
                (d0+w*x) (p+w*x^2)))) := by
      funext w
      simpa only [if_neg hn] using
        (thetaMixedOneRightJetSeriesTerm_two_zero_eq_B12 x n w)
    simp only [thetaCertificateCorrectionTerm, if_neg hn]
    rw [hfunc, MeasureTheory.integral_Ici_eq_integral_Ioi]
    simp only [integral_const_mul]
    ring

/-- The original B12 numerical correction is independently
summable for 0<x≤1, by the already-proven mixed-jet
Fubini theorem at right derivative order k=2. -/
theorem thetaCertificateCorrectionTerm_one_two_summable
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x (1:Fin 5) (2:Fin 5) n) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hjet : Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
    (thetaMixedOneRightJetSeries_integral_hasSum
      2 x 0 0 hx hx1 hz hz).summable
  have hfun :
      (fun n : ℕ =>
        thetaCertificateCorrectionTerm x (1:Fin 5) (2:Fin 5) n) =
      (fun n : ℕ =>
        (x^2/8) *
          (∫ w : ℝ, thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
    funext n
    exact thetaCertificateCorrectionTerm_one_two_eq_mixed_jet x n
  rw [hfun]
  exact hjet.mul_left (x^2/8)

/-- The entire B12 original numerical correction equals
x²/8 TIMES THE GENUINE mixed third derivative (one left
after two right derivatives) of the infinite transformed
Gaussian theta integral series at the Taylor origin.
No unproved derivative/sum/integral exchange occurs. -/
theorem thetaCertificateCorrectionSeries_one_two_eq_actual_mixed
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (∑' n : ℕ,
      thetaCertificateCorrectionTerm x (1:Fin 5) (2:Fin 5) n) =
      (x^2/8) *
        deriv (fun z : ℝ =>
          iteratedDeriv 2
            (fun y : ℝ =>
              ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hp := thetaGaussianSummableRightPatch_origin x hx
  have hFubini := (thetaMixedOneRightJetSeries_integral_hasSum
    2 x 0 0 hx hx1 hz hz).tsum_eq
  have hderiv := thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    2 x 0 0 hx hx1 hp hp
  have hsum :
      (∑' n : ℕ,
        ∫ w : ℝ,
          thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) =
      deriv (fun z : ℝ =>
        iteratedDeriv 2
          (fun y : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 :=
    hFubini.trans hderiv.symm
  calc
    (∑' n : ℕ,
      thetaCertificateCorrectionTerm x (1:Fin 5) (2:Fin 5) n) =
      (∑' n : ℕ,
        (x^2/8) *
          (∫ w : ℝ,
            thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
      apply tsum_congr
      intro n
      exact thetaCertificateCorrectionTerm_one_two_eq_mixed_jet x n
    _ = (x^2/8) * (∑' n : ℕ,
          ∫ w : ℝ,
            thetaMixedOneRightJetSeriesTerm 2 x 0 0 n w
              ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
      rw [tsum_mul_left]
    _ = _ := congrArg (fun z : ℝ => (x^2/8) * z) hsum

end W5
