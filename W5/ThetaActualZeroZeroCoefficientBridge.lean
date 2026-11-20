import W5.ThetaActualZeroOneSymmetryCoefficientBridge

/-!
# Exact B00 coefficient of the genuine transformed Gaussian theta integral series

The actual undifferentiated theta Gaussian integral series is
rigorously equal to the Lebesgue w-integral of its zero-jet
square-index series. At the Taylor origin each genuine Gaussian
factor equals 1, so its polynomial is exactly B00(d,q)=1.

We prove both orders (tsum of integrals, integral of tsum) without
new convergence/interchange axioms. This finishes the four entries
of the *integrated Gaussian component* of the leading 2x2 theta
coefficient block, not the still-unidentified unintegrated term.
-/

namespace W5
open MeasureTheory

/-- Exact zeroth theta Gaussian jet at the origin, with the
certificate coefficient polynomial B00=1 and n=0 convention. -/
theorem thetaHigherRightJetSeriesTerm_zero_zero_eq_B00
    (x : ℝ) (n : ℕ) (w : ℝ) :
    thetaHigherRightJetSeriesTerm 0 x 0 0 n w =
      if n = 0 then (0:ℝ) else
        let p : ℝ := (n:ℝ)^2
        let d0 : ℝ := (p-1)/x
        Real.exp (-(p-1)/x^2) *
          (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
            coefficientPolynomial (0:Fin 5) (0:Fin 5)
              (d0+w*x) (p+w*x^2)) := by
  by_cases hn : n = 0
  · simp [thetaHigherRightJetSeriesTerm, hn]
  · simp only [thetaHigherRightJetSeriesTerm, if_neg hn,
      thetaWeightedGaussianRightJet_zero,
      coefficientPolynomial_zero_zero]
    unfold thetaWeightedGaussianIntegrand
    rw [thetaGaussianModel_zero_zero]
    ring

/-- The actual undifferentiated transformed Gaussian theta
integral series equals the sum of w-integrals of the exact
original B00=1 Gaussian coefficient kernels. No Fubini needed. -/
theorem thetaGaussianIntegratedSeries_zero_zero_eq_B00_tsum_integral
    (x : ℝ) :
    (∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n 0) =
      ∑' n : ℕ,
        ∫ w : ℝ,
          (if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (0:Fin 5) (0:Fin 5)
                  (d0+w*x) (p+w*x^2)))
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  calc
    (∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n 0) =
      ∑' n : ℕ,
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
      apply tsum_congr
      intro n
      exact thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral x 0 0 n
    _ = _ := by
      apply tsum_congr
      intro n
      have hfun :
          (fun w : ℝ => thetaHigherRightJetSeriesTerm 0 x 0 0 n w) =
          (fun w : ℝ =>
            if n = 0 then (0:ℝ) else
              let p : ℝ := (n:ℝ)^2
              let d0 : ℝ := (p-1)/x
              Real.exp (-(p-1)/x^2) *
                (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                  coefficientPolynomial (0:Fin 5) (0:Fin 5)
                    (d0+w*x) (p+w*x^2))) := by
        funext w
        exact thetaHigherRightJetSeriesTerm_zero_zero_eq_B00 x n w
      rw [hfun]

/-- Fubini variant: one genuine Lebesgue integral of the
infinite theta square-index series with B00(d,q)=1.
No differentiation is required for the zeroth coefficient. -/
theorem thetaGaussianIntegratedSeries_zero_zero_eq_B00_integral_tsum
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n 0) =
      ∫ w : ℝ,
        (∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (0:Fin 5) (0:Fin 5)
                  (d0+w*x) (p+w*x^2)))
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hFubini :=
    (thetaHigherRightJetSeries_integral_hasSum 0 x 0 0
      hx hx1 hz hz).tsum_eq
  have hfun :
      (fun w : ℝ =>
        ∑' n : ℕ, thetaHigherRightJetSeriesTerm 0 x 0 0 n w) =
      (fun w : ℝ =>
        ∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (0:Fin 5) (0:Fin 5)
                  (d0+w*x) (p+w*x^2))) := by
    funext w
    apply tsum_congr
    intro n
    exact thetaHigherRightJetSeriesTerm_zero_zero_eq_B00 x n w
  calc
    (∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n 0) =
      ∑' n : ℕ,
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
      apply tsum_congr
      intro n
      exact thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral x 0 0 n
    _ = ∫ w : ℝ, ∑' n : ℕ,
      thetaHigherRightJetSeriesTerm 0 x 0 0 n w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := hFubini
    _ = _ := by rw [hfun]

end W5
