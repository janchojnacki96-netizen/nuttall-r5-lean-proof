import W5.ThetaGaussianDifferentiationPatch
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation through one theta w-integral: explicit analytic bridge

Mathlib's local dominated-differentiation theorem is applied to the
actual weighted Gaussian integrand. Its derivative, the common local
envelope, the envelope's integrability, and the parameter neighborhood
are provided by preceding W5 lemmas.

The theorem below still takes three precise assumptions about the
integrand: local a.e. strong measurability, integrability at v=0,
and strong measurability of the differentiated integrand.
Those must be discharged before the differentiation-under-integral
step is unconditional. This module says nothing about differentiating
the outer infinite sum over square indices.
-/

namespace W5
open MeasureTheory Filter
open scoped Topology

/-- The *explicit* integrand derivative provided by ordinary real
calculus, used as the derivative witness for Mathlib's theorem. -/
noncomputable def thetaWeightedGaussianRightDerivative
    (x p d0 u v w : ℝ) : ℝ :=
  Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
    (((-d0-p*u)-w*x*(1+x*u)) *
      thetaGaussianModel (d0+w*x) (p+w*x^2) u v)

/-- Application of Mathlib's dominated-differentiation theorem to
one genuine weighted theta Gaussian w-integral at v=0.

The pointwise bound and its w-integrability are *proved* internally;
only measurability and base-integrability remain as explicit premises.
The conclusion differentiates the actual half-line Lebesgue integral.
-/
theorem thetaWeightedGaussian_integral_hasDerivAt_of_measurable
    (x p d0 u : ℝ)
    (hp : 0 < p) (hu : |u| ≤ 1)
    (hxu : -(1:ℝ)/2 ≤ x*u)
    (hF_meas :
      ∀ᶠ z : ℝ in 𝓝 (0:ℝ),
        AEStronglyMeasurable
          (fun w : ℝ => thetaWeightedGaussianIntegrand x p d0 u z w)
          (volume.restrict (Set.Ioi (0:ℝ))))
    (hF_int :
      Integrable
        (fun w : ℝ => thetaWeightedGaussianIntegrand x p d0 u 0 w)
        (volume.restrict (Set.Ioi (0:ℝ))))
    (hF'_meas :
      AEStronglyMeasurable
        (fun w : ℝ => thetaWeightedGaussianRightDerivative x p d0 u 0 w)
        (volume.restrict (Set.Ioi (0:ℝ)))) :
    HasDerivAt
      (fun z : ℝ =>
        ∫ w : ℝ, thetaWeightedGaussianIntegrand x p d0 u z w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, thetaWeightedGaussianRightDerivative x p d0 u 0 w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) (0:ℝ) := by
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
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0:ℝ)))
    (F := fun z w => thetaWeightedGaussianIntegrand x p d0 u z w)
    (F' := fun z w => thetaWeightedGaussianRightDerivative x p d0 u z w)
    (bound := majorant)
    (s := thetaGaussianRightPatch x)
    (thetaGaussianRightPatch_mem_nhds x)
    hF_meas hF_int hF'_meas hbound hmajorant hdiff).2

end W5
