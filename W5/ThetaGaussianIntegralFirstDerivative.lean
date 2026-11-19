import W5.ThetaGaussianDominatedIntegralDerivative

/-!
# Removing the remaining measurability and integrability assumptions
for the first derivative of a single theta Gaussian w-integral

This module supplies the three concrete hypotheses in the dominated
differentiation bridge: strong measurability of the weighted integrand
at all parameters, integrability at the origin, and measurability of
the differentiated integrand. The input Gaussian majorant and the
derivative bound are already proved in preceding modules.

The resulting theorem is for ONE fixed square-index theta term.
Differentiation of the outer infinite square-index sum, and the
r=5 determinant-sign theorem, remain separate analytic obligations.
-/

namespace W5
open MeasureTheory Filter
open scoped Topology

/-- The full Gaussian theta w-integrand is measurable in w for each
fixed differentiation parameter. -/
theorem thetaWeightedGaussian_measurable
    (x p d0 u v : ℝ) :
    Measurable
      (fun w : ℝ => thetaWeightedGaussianIntegrand x p d0 u v w) := by
  unfold thetaWeightedGaussianIntegrand thetaGaussianModel
  fun_prop

/-- Likewise the explicit first derivative is measurable in w. -/
theorem thetaWeightedGaussianRightDerivative_measurable
    (x p d0 u v : ℝ) :
    Measurable
      (fun w : ℝ => thetaWeightedGaussianRightDerivative x p d0 u v w) := by
  unfold thetaWeightedGaussianRightDerivative thetaGaussianModel
  fun_prop

/-- The original weighted Gaussian theta w-integrand is absolutely
integrable on the positive half-line throughout the local positivity
patch, not merely majorized by an integrable expression. -/
theorem thetaWeightedGaussian_integrableOn
    (x p d0 u v : ℝ)
    (hp : 0 < p)
    (hu : -(1:ℝ)/2 ≤ x*u)
    (hv : -(1:ℝ)/2 ≤ x*v) :
    IntegrableOn
      (fun w : ℝ => thetaWeightedGaussianIntegrand x p d0 u v w)
      (Set.Ioi (0:ℝ)) volume := by
  have hmajorant := thetaGaussian_weighted_majorant_integrable x p d0 u v
  have hbound :
      ∀ᵐ w : ℝ ∂(volume.restrict (Set.Ioi (0:ℝ))),
        ‖thetaWeightedGaussianIntegrand x p d0 u v w‖ ≤
          Real.exp (-d0*(u+v)-p*u*v) *
            (1+w*x^2/p) * Real.exp (-((1:ℝ)/4)*w) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hbase : 0 ≤ 1+w*x^2/p := by
      have hterm : 0 ≤ w*x^2/p :=
        div_nonneg (mul_nonneg hw.le (sq_nonneg x)) hp.le
      linarith
    have hnonneg : 0 ≤ thetaWeightedGaussianIntegrand x p d0 u v w := by
      unfold thetaWeightedGaussianIntegrand thetaGaussianModel
      exact mul_nonneg
        (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hbase _))
        (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact thetaGaussian_weighted_uniform_bound x p d0 u v w
      hp hw.le hu hv
  exact hmajorant.mono'
    (thetaWeightedGaussian_measurable x p d0 u v).aestronglyMeasurable
    hbound

/-- The single transformed theta w-integral may be differentiated
at v=0, for any fixed p>0, when u belongs to the locally valid
coordinate patch. All measurability, base integrability, derivative,
locality and domination premises have been discharged.

**This theorem does NOT commute the infinite theta n-sum.** -/
theorem thetaWeightedGaussian_integral_hasDerivAt_zero
    (x p d0 u : ℝ)
    (hp : 0 < p)
    (hu : |u| ≤ 1)
    (hxu : -(1:ℝ)/2 ≤ x*u) :
    HasDerivAt
      (fun z : ℝ =>
        ∫ w : ℝ, thetaWeightedGaussianIntegrand x p d0 u z w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, thetaWeightedGaussianRightDerivative x p d0 u 0 w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) (0:ℝ) := by
  apply thetaWeightedGaussian_integral_hasDerivAt_of_measurable x p d0 u
    hp hu hxu
  · exact Filter.Eventually.of_forall (fun z =>
      (thetaWeightedGaussian_measurable x p d0 u z).aestronglyMeasurable)
  · exact thetaWeightedGaussian_integrableOn x p d0 u 0
      hp hxu (by norm_num)
  · exact (thetaWeightedGaussianRightDerivative_measurable
      x p d0 u 0).aestronglyMeasurable

end W5
