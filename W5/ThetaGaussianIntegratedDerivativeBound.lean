import W5.ThetaGaussianOpenPatchIntegralDerivative

/-!
# Summable envelope for derivatives of the integrated theta terms

The preceding branch bounds each *unintegrated* first derivative by the
separable Gaussian product majorant, uniformly on the small parameter box.
This module moves the estimate through the w-integral, producing a norm
bound for the actual derivative witness of the integrated n-th term.

This bridges the hypotheses needed for Mathlib's SmoothSeries theorem.
It does NOT by itself show the whole original theta series is
differentiable; local summability of the original (undifferentiated)
integrated terms is an independent obligation.
-/

namespace W5
open MeasureTheory

/-- Integrating the actual pointwise theta derivative bound yields an
explicit, summable majorant for the derivative of the n-th w-integral.
The constant depends only on x, not on n, u or v. -/
theorem thetaGaussian_nonzero_index_integrated_deriv_norm_le
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (u v : ℝ) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    ‖Real.exp (-((n:ℝ)^2-1)/x^2) *
      (∫ w : ℝ,
        thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w
        ∂(volume.restrict (Set.Ioi (0:ℝ))))‖ ≤
      (Real.exp (3/4)*(1/x+2)) *
        (∫ w : ℝ, thetaGaussianProductMajorant n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let C : ℝ := Real.exp (3/4)*(1/x+2)
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hF : Integrable
      (fun w : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w) μ := by
    exact thetaGaussian_nonzero_index_derivative_integrableOn
      x hx hx1 n hn u v hu hv
  have hM : Integrable
      (fun w : ℝ => C * thetaGaussianProductMajorant n w) μ := by
    exact (thetaGaussianProductMajorant_integrableOn n).const_mul C
  have hbound :
      ∀ᵐ w : ℝ ∂μ,
        ‖Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w‖ ≤
          C * thetaGaussianProductMajorant n w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    rw [Real.norm_eq_abs]
    exact thetaGaussian_nonzero_index_integrand_deriv_le_product
      x hx hx1 n hn u v w hw.le hu hv
  change
    ‖Real.exp (-((n:ℝ)^2-1)/x^2) *
      (∫ w : ℝ,
        thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w ∂μ)‖ ≤
      C * (∫ w : ℝ, thetaGaussianProductMajorant n w ∂μ)
  calc
    ‖Real.exp (-((n:ℝ)^2-1)/x^2) *
      (∫ w : ℝ,
        thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w ∂μ)‖ =
      ‖∫ w : ℝ,
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w ∂μ‖ := by
              rw [integral_const_mul]
    _ ≤ ∫ w : ℝ,
      ‖Real.exp (-((n:ℝ)^2-1)/x^2) *
        thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w‖ ∂μ :=
            norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℝ, C * thetaGaussianProductMajorant n w ∂μ :=
      integral_mono_ae hF.norm hM hbound
    _ = C * (∫ w : ℝ, thetaGaussianProductMajorant n w ∂μ) := by
      rw [integral_const_mul]

/-- Summability of the integrals of the actual first derivative
follows from the Fubini HasSum theorem, not from a merely formal
tsum expression. The index zero remains identically zero. -/
theorem thetaGaussianFirstDerivSeries_integrals_summable
    (x u : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) :
    Summable
      (fun n : ℕ =>
        ∫ w : ℝ, thetaGaussianFirstDerivSeriesTerm x u n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
  (thetaGaussianFirstDerivSeries_integral_hasSum x u hx hx1 hu).summable

/-- The differentiated theta series has a legitimate summation-
integration exchange at v=0 (without claiming that it is
already the derivative of the full theta series). -/
theorem thetaGaussianFirstDerivSeries_tsum_integral_eq
    (x u : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) :
    (∑' n : ℕ,
      ∫ w : ℝ, thetaGaussianFirstDerivSeriesTerm x u n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) =
    ∫ w : ℝ, ∑' n : ℕ,
      thetaGaussianFirstDerivSeriesTerm x u n w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) :=
  (thetaGaussianFirstDerivSeries_integral_hasSum x u hx hx1 hu).tsum_eq

end W5
