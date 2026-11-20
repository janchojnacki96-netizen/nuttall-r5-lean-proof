import W5.ThetaActualMixedElevenCoefficientBridge

/-!
# Exact B10 polynomial inside the genuine left derivative of theta integral series

The proof of the B11 bridge extends to the one-left/zero-right
coefficient. This connects the genuine u-derivative at the origin
with the same certificate polynomial B10(d,q)=-d used in the
numerical theta coefficient matrix.

The actual derivative-through-integral-and-infinite-sum theorem
was proved previously. We apply it at k=0, replace every
pointwise jet by the exact Gaussian polynomial identity, and
then use the verified Fubini theorem to reverse the sum/integral.

This identifies an integrated Gaussian component of the original
transformed theta representation, not its separate elementary
square-index term nor the original normalized Nuttall kernel.
-/

namespace W5

open MeasureTheory

/-- The exact first-left Gaussian derivative polynomial B10=-d
at the origin, including every weight and the n=0 convention. -/
theorem thetaMixedOneRightJetSeriesTerm_zero_zero_eq_B10
    (x : ℝ) (n : ℕ) (w : ℝ) :
    thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w =
      if n = 0 then (0:ℝ) else
        let p : ℝ := (n:ℝ)^2
        let d0 : ℝ := (p-1)/x
        Real.exp (-(p-1)/x^2) *
          (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
            coefficientPolynomial (1:Fin 5) (0:Fin 5)
              (d0+w*x) (p+w*x^2)) := by
  by_cases hn : n = 0
  · simp [thetaMixedOneRightJetSeriesTerm, hn]
  · simp only [thetaMixedOneRightJetSeriesTerm, if_neg hn,
      Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul]
    rw [coefficientPolynomial_one_zero]
    dsimp [thetaWeightedGaussianIntegrand, thetaGaussianModel,
      thetaWeightedGaussianRightMultiplier]
    simp only [mul_zero, zero_add, add_zero, sub_zero,
      Real.exp_zero, mul_one]
    ring

/-- Genuine first left derivative of the entire integrated theta
series at the origin, expressed as one integral of the original
B10 polynomial square-index series. -/
theorem thetaGaussianIntegratedSeries_left_deriv_eq_B10_integral_tsum
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    deriv
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 =
      ∫ w : ℝ,
        (∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (1:Fin 5) (0:Fin 5)
                  (d0+w*x) (p+w*x^2)))
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hz := thetaGaussianSummableRightPatch_origin x hx
  have h := thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    0 x 0 0 hx hx1 hz hz
  simp only [iteratedDeriv_zero] at h
  have hfun :
      (fun w : ℝ =>
        ∑' n : ℕ, thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w) =
      (fun w : ℝ =>
        ∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (1:Fin 5) (0:Fin 5)
                  (d0+w*x) (p+w*x^2))) := by
    funext w
    apply tsum_congr
    intro n
    exact thetaMixedOneRightJetSeriesTerm_zero_zero_eq_B10 x n w
  rw [hfun] at h
  exact h

/-- The genuine left derivative at the origin is the sum over n of
the actual Lebesgue integrals of the B10 polynomial. This uses
previously proved Fubini and no unjustified interchange. -/
theorem thetaGaussianIntegratedSeries_left_deriv_eq_B10_tsum_integral
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    deriv
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 =
      ∑' n : ℕ,
        ∫ w : ℝ,
          (if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (1:Fin 5) (0:Fin 5)
                  (d0+w*x) (p+w*x^2)))
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hz := thetaGaussianSummableRightPatch_origin x hx
  have hbase := thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    0 x 0 0 hx hx1 hz hz
  simp only [iteratedDeriv_zero] at hbase
  have hzero : |(0:ℝ)| ≤ x/8 := by positivity
  have hFubini := thetaMixedOneRightJetSeries_integral_hasSum
    0 x 0 0 hx hx1 hzero hzero
  calc
    deriv
        (fun z : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := hbase
    _ = ∑' n : ℕ,
      ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := hFubini.tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro n
      have hfunc :
          (fun w : ℝ => thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w) =
          (fun w : ℝ =>
            if n = 0 then (0:ℝ) else
              let p : ℝ := (n:ℝ)^2
              let d0 : ℝ := (p-1)/x
              Real.exp (-(p-1)/x^2) *
                (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                  coefficientPolynomial (1:Fin 5) (0:Fin 5)
                    (d0+w*x) (p+w*x^2))) := by
        funext w
        exact thetaMixedOneRightJetSeriesTerm_zero_zero_eq_B10 x n w
      rw [hfunc]

end W5
