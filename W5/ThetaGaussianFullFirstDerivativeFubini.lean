import W5.ThetaGaussianIntegratedSeriesDerivative

/-!
# An explicit first derivative of the full transformed theta n-series

This module combines the Mathlib SmoothSeries derivative result with
the genuine Fubini theorem proved for the *differentiated* theta
summands. The resulting derivative is not merely a formal sum of
single-index integrals: it is one Lebesgue integral of the complete
pointwise infinite differentiated theta series.

The identity concerns only the first v-derivative at zero of the
transformed Gaussian model, for fixed x and u in the small box.
It does not identify any Nuttall r=5 determinant or higher jet.
-/

namespace W5
open MeasureTheory

/-- The derivative witness for each n-th integrated theta term
is the integral of the actual n-th differentiated integrand,
with index zero handled explicitly. -/
theorem thetaGaussianIntegratedSeriesDerivative_zero_eq_integral
    (x u : ℝ) (n : ℕ) :
    thetaGaussianIntegratedSeriesDerivative x u n 0 =
      ∫ w : ℝ, thetaGaussianFirstDerivSeriesTerm x u n w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaGaussianIntegratedSeriesDerivative,
      thetaGaussianFirstDerivSeriesTerm]
  · change (if n = 0 then (0:ℝ) else
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          (∫ w : ℝ,
            thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u 0 w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) =
      ∫ w : ℝ,
        (if n = 0 then (0:ℝ) else
          Real.exp (-((n:ℝ)^2-1)/x^2) *
            thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u 0 w)
        ∂(volume.restrict (Set.Ioi (0:ℝ)))
    simp only [if_neg hn]
    rw [integral_const_mul]

/-- First derivative of the infinite sum of the transformed
theta w-integrals equals a single integral of the pointwise
infinite sum of the actual weighted first derivatives.

Both the differentiation of the n-series and the n-sum /
w-integral interchange have explicit Mathlib proofs in the
preceding W5 modules. -/
theorem thetaGaussianIntegratedSeries_deriv_zero_eq_integral_tsum
    (x u : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) :
    deriv
      (fun v : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x u n v)
      (0:ℝ) =
      ∫ w : ℝ,
        ∑' n : ℕ, thetaGaussianFirstDerivSeriesTerm x u n w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  rw [(thetaGaussianIntegratedSeries_hasDerivAt_zero x u hx hx1 hu).deriv]
  have heq :
      (fun n : ℕ => thetaGaussianIntegratedSeriesDerivative x u n 0) =
        (fun n : ℕ =>
          ∫ w : ℝ, thetaGaussianFirstDerivSeriesTerm x u n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
    funext n
    exact thetaGaussianIntegratedSeriesDerivative_zero_eq_integral x u n
  rw [heq]
  exact (thetaGaussianFirstDerivSeries_integral_hasSum x u hx hx1 hu).tsum_eq

end W5
