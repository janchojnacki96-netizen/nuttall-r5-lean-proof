import W5.ThetaB00CorrectionEqualsIntegratedSeries

/-!
# Exact B11 numerical correction equals the genuine theta mixed derivative

The B11 coefficient in the original independently defined numerical
theta certificate has a correction with the quarter-square scaling
x²/4. PR #60 identified the actual (1,1) mixed derivative of the
transformed Gaussian infinite series with the genuinely integrated
B11 polynomial. PR #64 isolated the original correction coefficient.

This module joins those two results, using the exact equality of
Ici 0 and Ioi 0 Lebesgue integrals and the previously verified Fubini
theorem. It does not make an unproved switch of an infinite sum,
integral or derivative.

It remains necessary to identify the independent n²-weighted
elementary coefficient and the original normalized Nuttall kernel;
no determinant sign is proved.
-/

namespace W5

open MeasureTheory

/-- The (1,1) correction to a single ORIGINAL theta coefficient
equals x²/4 times the genuine (1,1) Gaussian mixed jet integral.
The zero square index is treated explicitly. -/
theorem thetaCertificateCorrectionTerm_one_one_eq_mixed_integral
    (x : ℝ) (n : ℕ) :
    thetaCertificateCorrectionTerm x (1:Fin 5) (1:Fin 5) n =
      (x^2/4) *
        (∫ w : ℝ,
          thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateCorrectionTerm, thetaMixedOneRightJetSeriesTerm]
  · have hfunc :
        (fun w : ℝ => thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w) =
        (fun w : ℝ =>
          let p : ℝ := (n:ℝ)^2
          let d0 : ℝ := (p-1)/x
          Real.exp (-(p-1)/x^2) *
            (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
              coefficientPolynomial (1:Fin 5) (1:Fin 5)
                (d0+w*x) (p+w*x^2))) := by
      funext w
      simpa only [if_neg hn] using
        (thetaMixedOneRightJetSeriesTerm_one_zero x n w)
    simp only [thetaCertificateCorrectionTerm, if_neg hn]
    rw [hfunc]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [integral_const_mul]
    ring

/-- The WHOLE ORIGINAL numerical B11 correction is precisely
x²/4 times the genuine (1,1) mixed derivative of the infinite
transformed Gaussian theta integral series at the Taylor origin.
The theorem is unconditional on 0<x≤1, without postulated
interchanges, positivity or numerical bounds. -/
theorem thetaCertificateCorrectionSeries_one_one_eq_actual_derivative
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (∑' n : ℕ,
      thetaCertificateCorrectionTerm x (1:Fin 5) (1:Fin 5) n) =
      (x^2/4) *
        deriv
          (fun z : ℝ =>
            iteratedDeriv 1
              (fun y : ℝ =>
                ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hpatch := thetaGaussianSummableRightPatch_origin x hx
  have hFubini := (thetaMixedOneRightJetSeries_integral_hasSum
    1 x 0 0 hx hx1 hz hz).tsum_eq
  have hderiv := thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    1 x 0 0 hx hx1 hpatch hpatch
  have hsum :
      (∑' n : ℕ,
        ∫ w : ℝ,
          thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) =
      deriv
        (fun z : ℝ =>
          iteratedDeriv 1
            (fun y : ℝ =>
              ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 :=
    hFubini.trans hderiv.symm
  calc
    (∑' n : ℕ,
      thetaCertificateCorrectionTerm x (1:Fin 5) (1:Fin 5) n) =
      (∑' n : ℕ,
        (x^2/4) *
          (∫ w : ℝ,
            thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
      apply tsum_congr
      intro n
      exact thetaCertificateCorrectionTerm_one_one_eq_mixed_integral x n
    _ = (x^2/4) * (∑' n : ℕ,
          ∫ w : ℝ,
            thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w
              ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
      rw [tsum_mul_left]
    _ = _ := congrArg (fun z : ℝ => (x^2/4) * z) hsum

end W5
