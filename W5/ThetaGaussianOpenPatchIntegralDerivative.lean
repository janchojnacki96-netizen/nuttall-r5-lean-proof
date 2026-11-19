import W5.ThetaGaussianFirstDerivativeFubini
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiability of every single-index theta w-integral on an open patch

PR #28 gives an unconditional derivative only at v=0. In order to
differentiate the *whole n-series* via Mathlib's SmoothSeries theorem,
each summand must be differentiable on a common open preconnected set.

Here the same dominated parametric-integral theorem is applied at an
arbitrary v in the already constructed open thetaGaussianRightPatch x.
This upgrades single-term differentiability from a single point to an
open neighborhood. It still does not exchange derivative and n-tsum.
-/

namespace W5
open MeasureTheory Filter
open scoped Topology

/-- The weighted theta Gaussian w-integral is differentiable at every
v of the actual open Gaussian-right patch. Unlike PR #28 this theorem
is not restricted to v=0. All measurability and integrability
hypotheses are discharged. -/
theorem thetaWeightedGaussian_integral_hasDerivAt_on_rightPatch
    (x p d0 u v : ℝ)
    (hp : 0 < p) (hu : |u| ≤ 1)
    (hxu : -(1:ℝ)/2 ≤ x*u)
    (hv : v ∈ thetaGaussianRightPatch x) :
    HasDerivAt
      (fun z : ℝ =>
        ∫ w : ℝ, thetaWeightedGaussianIntegrand x p d0 u z w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, thetaWeightedGaussianRightDerivative x p d0 u v w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) v := by
  let majorant : ℝ → ℝ := fun w =>
    ((|d0|+|p|)+w*(|x| *(1+|x|))) *
      (Real.exp (2*|d0|+|p|) *
        (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w))
  have hbound :
      ∀ᵐ w : ℝ ∂(volume.restrict (Set.Ioi (0:ℝ))),
        ∀ z ∈ thetaGaussianRightPatch x,
          ‖thetaWeightedGaussianRightDerivative x p d0 u z w‖ ≤ majorant w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    intro z hz
    obtain ⟨hzabs, hzx⟩ := thetaGaussianRightPatch_bounds x z hz
    have hb := thetaWeightedGaussian_actual_deriv_uniform_envelope
      x p d0 u z w hp hw.le hu hzabs hxu hzx
    rw [(thetaWeightedGaussian_hasDerivAt_right x p d0 u z w).deriv] at hb
    simpa only [thetaWeightedGaussianRightDerivative, majorant, Real.norm_eq_abs] using hb
  have hmajorant :
      Integrable majorant (volume.restrict (Set.Ioi (0:ℝ))) := by
    exact thetaGaussian_first_deriv_uniform_envelope_integrable x p d0
  have hdiff :
      ∀ᵐ w : ℝ ∂(volume.restrict (Set.Ioi (0:ℝ))),
        ∀ z ∈ thetaGaussianRightPatch x,
          HasDerivAt
            (fun y : ℝ => thetaWeightedGaussianIntegrand x p d0 u y w)
            (thetaWeightedGaussianRightDerivative x p d0 u z w) z := by
    filter_upwards with w
    intro z _
    exact thetaWeightedGaussian_hasDerivAt_right x p d0 u z w
  have hF_meas :
      ∀ᶠ z : ℝ in 𝓝 v,
        AEStronglyMeasurable
          (fun w : ℝ => thetaWeightedGaussianIntegrand x p d0 u z w)
          (volume.restrict (Set.Ioi (0:ℝ))) :=
    Filter.Eventually.of_forall (fun z =>
      (thetaWeightedGaussian_measurable x p d0 u z).aestronglyMeasurable)
  have hF_int :
      Integrable (fun w : ℝ => thetaWeightedGaussianIntegrand x p d0 u v w)
        (volume.restrict (Set.Ioi (0:ℝ))) :=
    thetaWeightedGaussian_integrableOn x p d0 u v
      hp hxu (thetaGaussianRightPatch_bounds x v hv).2
  have hF'_meas :
      AEStronglyMeasurable
        (fun w : ℝ => thetaWeightedGaussianRightDerivative x p d0 u v w)
        (volume.restrict (Set.Ioi (0:ℝ))) :=
    (thetaWeightedGaussianRightDerivative_measurable
      x p d0 u v).aestronglyMeasurable
  have hnhds : thetaGaussianRightPatch x ∈ 𝓝 v :=
    (thetaGaussianRightPatch_isOpen x).mem_nhds hv
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0:ℝ)))
    (F := fun z w => thetaWeightedGaussianIntegrand x p d0 u z w)
    (F' := fun z w => thetaWeightedGaussianRightDerivative x p d0 u z w)
    (bound := majorant)
    (s := thetaGaussianRightPatch x)
    hnhds hF_meas hF_int hF'_meas hbound hmajorant hdiff).2

/-- The same genuine derivative after the outer theta square-index
Gaussian factor, valid at every point of the common open patch. -/
theorem thetaGaussian_nonzero_index_integral_hasDerivAt_on_rightPatch
    (x : ℝ) (n : ℕ) (hn : 1 ≤ n) (u v : ℝ)
    (hu : |u| ≤ 1) (hxu : -(1:ℝ)/2 ≤ x*u)
    (hv : v ∈ thetaGaussianRightPatch x) :
    HasDerivAt
      (fun z : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          (∫ w : ℝ,
            thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u z w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))))
      (Real.exp (-((n:ℝ)^2-1)/x^2) *
        (∫ w : ℝ,
          thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))) v := by
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : 0 < (n:ℝ)^2 := by nlinarith
  exact
    (thetaWeightedGaussian_integral_hasDerivAt_on_rightPatch
      x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v hp hu hxu hv).const_mul
        (Real.exp (-((n:ℝ)^2-1)/x^2))

end W5
