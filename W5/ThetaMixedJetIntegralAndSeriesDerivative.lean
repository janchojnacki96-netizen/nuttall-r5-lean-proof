import W5.ThetaMixedJetFubini
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Genuine one-left / arbitrary-right mixed derivatives of theta series

The mixed-jet Fubini and uniform n-w majorants from PRs #55-#57
permit the standard dominated differentiation argument in u.
For each k, first differentiate the integrated kth right jet under
the Lebesgue w-integral, then differentiate the entire n-sum using
Mathlib's connected-patch summable-series theorem.

Finally the existing local identification of all genuine right
derivatives with their integrated right-jet sums transfers this
result to the ORIGINAL transformed Gaussian theta-series definition.

This establishes mixed (one left, k right) derivatives for every k
inside the common open parameter patch. General multiple-left jets,
the original normalized Nuttall kernel and its determinant signs
remain independent tasks.
-/

namespace W5
open MeasureTheory Filter
open scoped Topology

/-- Differentiating a single integrated kth right jet in u gives
the integral of the genuine (1,k) mixed jet on the common patch.
The interchange has an integrable bound independent of u. -/
theorem thetaHigherRightJetSeries_integral_hasDerivAt_left_on_patch
    (k : ℕ) (x v : ℝ) (n : ℕ) (u : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : |v| ≤ x/8)
    (hu : u ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt
      (fun z : ℝ =>
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x z v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, thetaMixedOneRightJetSeriesTerm k x u v n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) u := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let s : Set ℝ := thetaGaussianSummableRightPatch x
  let majorant : ℝ → ℝ := fun w =>
    thetaMixedJetIndexFactor k x n * thetaMixedJetTailFactor k w
  have hbound :
      ∀ᵐ w : ℝ ∂μ,
        ∀ z ∈ s,
          ‖thetaMixedOneRightJetSeriesTerm k x z v n w‖ ≤
            majorant w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    intro z hz
    exact thetaMixedOneRightJetSeriesTerm_norm_le_separable
      k x z v n w hx hx1
        (thetaGaussianSummableRightPatch_abs_le x z hz) hv hw.le
  have hmajorant : Integrable majorant μ :=
    (thetaMixedJetTailFactor_integrableOn k).const_mul
      (thetaMixedJetIndexFactor k x n)
  have hdiff :
      ∀ᵐ w : ℝ ∂μ,
        ∀ z ∈ s,
          HasDerivAt
            (fun y : ℝ => thetaHigherRightJetSeriesTerm k x y v n w)
            (thetaMixedOneRightJetSeriesTerm k x z v n w) z := by
    filter_upwards with w
    intro z _
    exact thetaHigherRightJetSeriesTerm_hasDerivAt_left k x z v n w
  have hF_meas :
      ∀ᶠ z : ℝ in 𝓝 u,
        AEStronglyMeasurable
          (fun w : ℝ => thetaHigherRightJetSeriesTerm k x z v n w) μ :=
    Filter.Eventually.of_forall (fun z =>
      (thetaHigherRightJetSeriesTerm_measurable k x z v n).aestronglyMeasurable)
  have huabs : |u| ≤ x/8 :=
    thetaGaussianSummableRightPatch_abs_le x u hu
  have hF_int : Integrable
      (thetaHigherRightJetSeriesTerm k x u v n) μ :=
    thetaHigherRightJetSeriesTerm_integrableOn k x u v n hx hx1 huabs hv
  have hF'_meas : AEStronglyMeasurable
      (thetaMixedOneRightJetSeriesTerm k x u v n) μ :=
    (thetaMixedOneRightJetSeriesTerm_measurable k x u v n).aestronglyMeasurable
  have hnhds : s ∈ 𝓝 u :=
    (thetaGaussianSummableRightPatch_isOpen x).mem_nhds hu
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun z w => thetaHigherRightJetSeriesTerm k x z v n w)
    (F' := fun z w => thetaMixedOneRightJetSeriesTerm k x z v n w)
    (bound := majorant)
    (s := s)
    hnhds hF_meas hF_int hF'_meas hbound hmajorant hdiff).2

/-- Differentiating the FULL infinite n-sum of integrated kth
right jets in u: the derivative is the n-sum of genuine mixed
integrated jets. Both the single-term differentiation and
uniform summable derivative bound have been proved. -/
theorem thetaHigherRightJet_integratedSeries_hasDerivAt_left
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : |v| ≤ x/8)
    (hu : u ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x z v n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∑' n : ℕ,
        ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) u := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let s : Set ℝ := thetaGaussianSummableRightPatch x
  let f : ℕ → ℝ → ℝ := fun n z =>
    ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x z v n w ∂μ
  let g : ℕ → ℝ → ℝ := fun n z =>
    ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm k x z v n w ∂μ
  let a : ℕ → ℝ := fun n =>
    thetaMixedJetIndexFactor k x n *
      (∫ w : ℝ, thetaMixedJetTailFactor k w ∂μ)
  have hA : Summable a :=
    (thetaMixedJetIndexFactor_summable k x).mul_right
      (∫ w : ℝ, thetaMixedJetTailFactor k w ∂μ)
  have hopen : IsOpen s := thetaGaussianSummableRightPatch_isOpen x
  have hconn : IsPreconnected s :=
    thetaGaussianSummableRightPatch_isPreconnected x
  have hzero : (0:ℝ) ∈ s :=
    thetaGaussianSummableRightPatch_zero_mem x hx
  have hdiff : ∀ n : ℕ, ∀ z : ℝ, z ∈ s →
      HasDerivAt (f n) (g n z) z := by
    intro n z hz
    exact thetaHigherRightJetSeries_integral_hasDerivAt_left_on_patch
      k x v n z hx hx1 hv hz
  have hbound : ∀ n : ℕ, ∀ z : ℝ, z ∈ s →
      ‖g n z‖ ≤ a n := by
    intro n z hz
    exact thetaMixedOneRightJetSeriesTerm_integral_norm_le
      k x z v n hx hx1
        (thetaGaussianSummableRightPatch_abs_le x z hz) hv
  have h0abs : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hbase : Summable (fun n : ℕ => f n 0) :=
    thetaHigherRightJetSeries_integrals_summable
      k x 0 v hx hx1 h0abs hv
  change HasDerivAt (fun z : ℝ => ∑' n : ℕ, f n z)
    (∑' n : ℕ, g n u) u
  exact hasDerivAt_tsum_of_isPreconnected hA hopen hconn
    hdiff hbound hzero hbase hu

/-- One actual u-derivative of the full kth right-jet n-sum
equals ONE integral of the entire mixed theta-jet series. -/
theorem thetaHigherRightJet_integratedSeries_deriv_left_eq_integral_tsum
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : |v| ≤ x/8)
    (hu : u ∈ thetaGaussianSummableRightPatch x) :
    deriv
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x z v n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))
      u =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaMixedOneRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  rw [(thetaHigherRightJet_integratedSeries_hasDerivAt_left
    k x u v hx hx1 hv hu).deriv]
  exact (thetaMixedOneRightJetSeries_integral_hasSum
    k x u v hx hx1
      (thetaGaussianSummableRightPatch_abs_le x u hu) hv).tsum_eq

/-- GENUINE mixed derivative of the original infinite transformed
Gaussian theta series: one left derivative after k right derivatives.
The entire interchange of this (1,k) mixed derivative with BOTH
the improper w-integral and infinite n-sum is proved in this chain. -/
theorem thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : v ∈ thetaGaussianSummableRightPatch x)
    (hu : u ∈ thetaGaussianSummableRightPatch x) :
    deriv
      (fun z : ℝ =>
        iteratedDeriv k
          (fun y : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) v) u =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaMixedOneRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hvabs : |v| ≤ x/8 :=
    thetaGaussianSummableRightPatch_abs_le x v hv
  have heventual :
      (fun z : ℝ =>
        iteratedDeriv k
          (fun y : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) v) =ᶠ[𝓝 u]
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x z v n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
    filter_upwards [(thetaGaussianSummableRightPatch_isOpen x).mem_nhds hu]
      with z hz
    have hzabs : |z| ≤ x/8 :=
      thetaGaussianSummableRightPatch_abs_le x z hz
    have hfun :
        (fun y : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) =
        (fun y : ℝ =>
          ∑' n : ℕ,
            ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x z y n w
              ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
      funext y
      apply tsum_congr
      intro n
      exact thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral x z y n
    rw [hfun]
    exact thetaHigherRightJet_integratedSeries_iteratedDeriv_eq
      k x z v hx hx1 hzabs hv
  rw [Filter.EventuallyEq.deriv_eq heventual]
  exact thetaHigherRightJet_integratedSeries_deriv_left_eq_integral_tsum
    k x u v hx hx1 hvabs hu

end W5
