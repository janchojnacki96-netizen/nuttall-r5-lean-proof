import W5.ThetaGaussianIntegralFirstDerivative
import W5.ThetaGaussianActualDerivativeProductBound

/-!
# Integrated square-index theta term: a genuine first derivative

This module joins the previously separate proofs:
* the unconditional derivative of one weighted Gaussian w-integral,
* the Gaussian square-index majorant for its differentiated integrand.

The natural index zero is excluded because the weighted formula contains
division by n². The original theta series defines that index to vanish.

This is still an indexwise derivative theorem, NOT differentiation of the
entire theta infinite series or a proof of the Nuttall r=5 sign claim.
-/

namespace W5

open MeasureTheory

/-- The outer theta damping factor is constant in the v-parameter;
thus the single-index integral derivative carries this factor. -/
theorem thetaGaussian_nonzero_index_integral_hasDerivAt_zero
    (x : ℝ) (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu : |u| ≤ 1) (hxu : -(1:ℝ)/2 ≤ x*u) :
    HasDerivAt
      (fun v : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          (∫ w : ℝ,
            thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u v w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))))
      (Real.exp (-((n:ℝ)^2-1)/x^2) *
        (∫ w : ℝ,
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u 0 w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))) (0:ℝ) := by
  have hnR : (1:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast hn
  have hp : 0 < (n:ℝ)^2 := by
    nlinarith
  exact
    (thetaWeightedGaussian_integral_hasDerivAt_zero
      x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u
      hp hu hxu).const_mul
        (Real.exp (-((n:ℝ)^2-1)/x^2))

/-- The actual ordinary derivative of the integrated single-index
theta term has an explicit integral formula at v=0. -/
theorem thetaGaussian_nonzero_index_integral_deriv_zero
    (x : ℝ) (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu : |u| ≤ 1) (hxu : -(1:ℝ)/2 ≤ x*u) :
    deriv
      (fun v : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          (∫ w : ℝ,
            thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u v w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))))
      (0:ℝ) =
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        (∫ w : ℝ,
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u 0 w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  exact (thetaGaussian_nonzero_index_integral_hasDerivAt_zero
    x n hn u hu hxu).deriv


/-- The explicit derivative witness used under the w-integral
is exactly the weighted derivative estimated by the Gaussian
square-index majorant. This links PR #28 to PR #31 pointwise. -/
theorem thetaGaussian_nonzero_index_integrand_deriv_le_product
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (u v w : ℝ) (hw : 0 ≤ w)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    |Real.exp (-((n:ℝ)^2-1)/x^2) *
      thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) u v w| ≤
      (Real.exp (3/4)*(1/x+2)) * thetaGaussianProductMajorant n w := by
  have hrewrite :
      thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w =
        Real.exp (-w) * (1+w*x^2/(n:ℝ)^2)^((1:ℝ)/4) *
          deriv (fun z : ℝ =>
            thetaGaussianModel (((n:ℝ)^2-1)/x+w*x)
              ((n:ℝ)^2+w*x^2) u z) v := by
    calc
      thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w =
        deriv (fun z : ℝ =>
          thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u z w) v := by
              exact (thetaWeightedGaussian_hasDerivAt_right x ((n:ℝ)^2)
                (((n:ℝ)^2-1)/x) u v w).deriv.symm
      _ = Real.exp (-w) * (1+w*x^2/(n:ℝ)^2)^((1:ℝ)/4) *
          deriv (fun z : ℝ =>
            thetaGaussianModel (((n:ℝ)^2-1)/x+w*x)
              ((n:ℝ)^2+w*x^2) u z) v :=
          thetaWeightedGaussian_right_deriv_eq_weighted
            x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v w
  have h := thetaGaussian_nonzero_index_first_deriv_le_product
    x hx hx1 n hn u v w hw hu hv
  rw [← hrewrite] at h
  exact h

/-- For any nonzero theta index, the actual derivative witness
including its outer theta factor is absolutely integrable on
w > 0. The proof uses the Gaussian product majorant, rather
than a non-summable per-index estimate. -/
theorem thetaGaussian_nonzero_index_derivative_integrableOn
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (u v : ℝ) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    IntegrableOn
      (fun w : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w)
      (Set.Ioi (0:ℝ)) volume := by
  let C : ℝ := Real.exp (3/4)*(1/x+2)
  have hmajorant : Integrable
      (fun w : ℝ => C * thetaGaussianProductMajorant n w)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    exact (thetaGaussianProductMajorant_integrableOn n).const_mul C
  have hmeas :
      AEStronglyMeasurable
        (fun w : ℝ =>
          Real.exp (-((n:ℝ)^2-1)/x^2) *
            thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u v w)
        (volume.restrict (Set.Ioi (0:ℝ))) := by
    exact (measurable_const.mul
      (thetaWeightedGaussianRightDerivative_measurable x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) u v)).aestronglyMeasurable
  have hbound :
      ∀ᵐ w : ℝ ∂(volume.restrict (Set.Ioi (0:ℝ))),
        ‖Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w‖ ≤
          ‖C * thetaGaussianProductMajorant n w‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hM : 0 ≤ thetaGaussianProductMajorant n w := by
      unfold thetaGaussianProductMajorant
      have hw0 : 0 ≤ w := le_of_lt hw
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC hM)]
    exact thetaGaussian_nonzero_index_integrand_deriv_le_product
      x hx hx1 n hn u v w (le_of_lt hw) hu hv
  change Integrable
    (fun w : ℝ =>
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w)
    (volume.restrict (Set.Ioi (0:ℝ)))
  exact hmajorant.mono' hmeas hbound

end W5
