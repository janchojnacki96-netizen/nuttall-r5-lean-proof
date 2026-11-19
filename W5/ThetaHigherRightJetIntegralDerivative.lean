import W5.ThetaHigherRightJetIntegratedBound
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiate every fixed-order theta right jet under its w-integral

For every natural order k, this module uses the kth and (k+1)st
Gaussian jet formulas, together with the all-order separable
majorant and the previous integrability lemma, to justify:

  d/dv (∫_0^∞ jet_k(n,v,w) dw) = ∫_0^∞ jet_(k+1)(n,v,w) dw

on the common open parameter patch (-x/8, x/8), uniformly in
the summation index n (the zero index is exactly zero).

This differentiates EACH w-integral, not yet the whole n-sum.
The theorem has no unproved analytic side assumptions.
-/

namespace W5

open MeasureTheory Filter
open scoped Topology

/-- Every kth integrated theta summand is differentiable, and its
derivative is exactly the integral of the (k+1)st genuine jet.
This includes n=0 and holds throughout the common theta patch. -/
theorem thetaHigherRightJetSeries_integral_hasDerivAt_on_patch
    (k : ℕ) (x u : ℝ) (n : ℕ) (v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8)
    (hv : v ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt
      (fun z : ℝ =>
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u z n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, thetaHigherRightJetSeriesTerm (k+1) x u v n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) v := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let s : Set ℝ := thetaGaussianSummableRightPatch x
  let majorant : ℝ → ℝ := fun w =>
    thetaHigherJetIndexFactor (k+1) x n *
      thetaHigherJetTailFactor (k+1) w
  have hbound :
      ∀ᵐ w : ℝ ∂μ,
        ∀ z ∈ s,
          ‖thetaHigherRightJetSeriesTerm (k+1) x u z n w‖ ≤
            majorant w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    intro z hz
    exact thetaHigherRightJetSeriesTerm_norm_le
      (k+1) x u z n w hx hx1 hu
      (thetaGaussianSummableRightPatch_abs_le x z hz) hw.le
  have hmajorant : Integrable majorant μ := by
    exact (thetaHigherJet_full_w_factor_integrableOn (k+1)).const_mul
      (thetaHigherJetIndexFactor (k+1) x n)
  have hdiff :
      ∀ᵐ w : ℝ ∂μ,
        ∀ z ∈ s,
          HasDerivAt
            (fun y : ℝ => thetaHigherRightJetSeriesTerm k x u y n w)
            (thetaHigherRightJetSeriesTerm (k+1) x u z n w) z := by
    filter_upwards with w
    intro z _
    by_cases hn : n = 0
    · subst n
      change HasDerivAt (fun _ : ℝ => (0:ℝ)) (0:ℝ) z
      exact hasDerivAt_const z 0
    · have h :=
        (thetaWeightedGaussianRightJet_hasDerivAt
          k x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u z w).const_mul
            (Real.exp (-((n:ℝ)^2-1)/x^2))
      change HasDerivAt
        (fun y : ℝ =>
          if n = 0 then (0:ℝ) else
            Real.exp (-((n:ℝ)^2-1)/x^2) *
              thetaWeightedGaussianRightJet k x ((n:ℝ)^2)
                (((n:ℝ)^2-1)/x) u y w)
        (if n = 0 then (0:ℝ) else
          Real.exp (-((n:ℝ)^2-1)/x^2) *
            thetaWeightedGaussianRightJet (k+1) x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u z w) z
      simpa only [if_neg hn] using h
  have hF_meas :
      ∀ᶠ z : ℝ in 𝓝 v,
        AEStronglyMeasurable
          (thetaHigherRightJetSeriesTerm k x u z n) μ :=
    Filter.Eventually.of_forall (fun z =>
      (thetaHigherRightJetSeriesTerm_measurable k x u z n).aestronglyMeasurable)
  have hvabs : |v| ≤ x/8 :=
    thetaGaussianSummableRightPatch_abs_le x v hv
  have hF_int :
      Integrable (thetaHigherRightJetSeriesTerm k x u v n) μ :=
    thetaHigherRightJetSeriesTerm_integrableOn
      k x u v n hx hx1 hu hvabs
  have hF'_meas :
      AEStronglyMeasurable
        (thetaHigherRightJetSeriesTerm (k+1) x u v n) μ :=
    (thetaHigherRightJetSeriesTerm_measurable (k+1) x u v n).aestronglyMeasurable
  have hnhds : s ∈ 𝓝 v :=
    (thetaGaussianSummableRightPatch_isOpen x).mem_nhds hv
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun z w => thetaHigherRightJetSeriesTerm k x u z n w)
    (F' := fun z w => thetaHigherRightJetSeriesTerm (k+1) x u z n w)
    (bound := majorant)
    (s := s)
    hnhds hF_meas hF_int hF'_meas hbound hmajorant hdiff).2

end W5
