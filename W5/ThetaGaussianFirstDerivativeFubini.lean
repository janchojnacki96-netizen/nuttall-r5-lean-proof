import W5.ThetaGaussianIntegratedIndexBridge
import W5.ThetaSeparableFubini

/-!
# Actual theta derivative series: interchanging n-summation with w-integration

The index zero is explicitly set to zero, as in the original theta
series. For n >= 1 we use the genuine derivative of the weighted
Gaussian integrand, including its outer theta Gaussian decay.

By PR #32 the derivative is pointwise bounded by a product of:
  C(x) * (n²+1) * exp(-47*n²/64)
and
  (w²+w+1) * exp(-w/4).
The first factor is summable over n and the second is integrable
over w>0. This module applies the existing generic, genuine
Mathlib-based dominated convergence / Fubini theorem.

This proves interchange of n-sum with the w-integral for the
differentiated integrand. It does NOT yet justify differentiation
of the entire n-sum with respect to the parameter v, nor prove r=5.
-/

namespace W5
open MeasureTheory

/-- The actual differentiated theta Gaussian summand (at v=0)
after its outer Gaussian factor; index zero is defined to vanish. -/
noncomputable def thetaGaussianFirstDerivSeriesTerm
    (x u : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  if n = 0 then 0 else
    Real.exp (-((n:ℝ)^2-1)/x^2) *
      thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) u 0 w

/-- Strong measurability required by dominated convergence is
unconditional for each natural-number index. -/
theorem thetaGaussianFirstDerivSeriesTerm_measurable
    (x u : ℝ) (n : ℕ) :
    Measurable (thetaGaussianFirstDerivSeriesTerm x u n) := by
  by_cases hn : n = 0
  · subst n
    change Measurable (fun _ : ℝ => (0:ℝ))
    exact measurable_const
  · have hm : Measurable (fun w : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u 0 w) :=
      measurable_const.mul
        (thetaWeightedGaussianRightDerivative_measurable
          x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u 0)
    change Measurable (fun w : ℝ =>
      if n = 0 then (0:ℝ) else
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u 0 w)
    simpa only [if_neg hn] using hm

/-- In the small coordinate box, the series of integrals of
actual theta first derivatives equals the integral of their
infinite n-series, by an explicit separable summable/integrable
envelope. This is a HasSum theorem, not just a formal tsum identity. -/
theorem thetaGaussianFirstDerivSeries_integral_hasSum
    (x u : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) :
    HasSum
      (fun n : ℕ =>
        ∫ w : ℝ, thetaGaussianFirstDerivSeriesTerm x u n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, ∑' n : ℕ,
        thetaGaussianFirstDerivSeriesTerm x u n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let C : ℝ := Real.exp (3/4)*(1/x+2)
  let a : ℕ → ℝ := fun n =>
    C * (((n:ℝ)^2+1)*Real.exp (-((47:ℝ)/64)*(n:ℝ)^2))
  let b : ℝ → ℝ := fun w =>
    (w^2+w+1)*Real.exp (-((1:ℝ)/4)*w)
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hA : Summable a := by
    change Summable (fun n : ℕ =>
      C * (((n:ℝ)^2+1)*Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)))
    exact thetaGaussianProductMajorant_index_factor_summable.mul_left C
  have hB : Integrable b μ := by
    change IntegrableOn b (Set.Ioi (0:ℝ)) volume
    simpa only [b, one_mul] using
      (thetaGaussian_quadratic_exp_integrable (1:ℝ) 1 1)
  have hF : ∀ n : ℕ,
      AEStronglyMeasurable (thetaGaussianFirstDerivSeriesTerm x u n) μ := by
    intro n
    exact (thetaGaussianFirstDerivSeriesTerm_measurable x u n).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ∀ n : ℕ, ‖thetaGaussianFirstDerivSeriesTerm x u n w‖ ≤ a n*b w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw n
    have hw0 : 0 ≤ w := le_of_lt hw
    by_cases hn : n = 0
    · have hC : 0 ≤ C := by
        dsimp [C]
        positivity
      have ha : 0 ≤ a n := by
        dsimp [a]
        positivity
      have hb : 0 ≤ b w := by
        dsimp [b]
        positivity
      simpa only [thetaGaussianFirstDerivSeriesTerm, if_pos hn,
        norm_zero] using (mul_nonneg ha hb)
    · have hn1 : 1 ≤ n := by omega
      have hv : |(0:ℝ)| ≤ x/8 := by
        simp only [abs_zero]
        positivity
      have h := thetaGaussian_nonzero_index_integrand_deriv_le_product
        x hx hx1 n hn1 u 0 w hw0 hu hv
      have heq : a n*b w =
          C * thetaGaussianProductMajorant n w := by
        dsimp [a, b, thetaGaussianProductMajorant]
        ring
      rw [heq]
      simpa only [thetaGaussianFirstDerivSeriesTerm,
        if_neg hn, Real.norm_eq_abs, C] using h
  exact hasSum_integral_of_separable_bound μ
    (thetaGaussianFirstDerivSeriesTerm x u) a b
    hA hB hF hbound

end W5
