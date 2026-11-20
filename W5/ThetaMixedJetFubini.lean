import W5.ThetaMixedJetSeparableEnvelope
import W5.ThetaSeparableFubini

/-!
# Fubini and integrated bounds for genuine mixed theta jets

The exact one-left/k-right Gaussian jet now has a proven separable
Gaussian/exponential upper bound (previous module). We establish its
strong measurability, integrability at each square index, a uniform
bound on its Lebesgue integral, and Fubini for the full infinite
square-index sum, at EVERY fixed k.

This is the mixed-jet analog of ThetaHigherRightJetFubini. It is
not yet differentiation of the summed integrated kth right jets
with respect to the *left* parameter; that requires the standard
dominated-derivative argument in another module.
-/

namespace W5
open MeasureTheory

/-- Every mixed Gaussian jet is measurable as a function of w,
including the zero-index term. -/
theorem thetaMixedOneRightJetSeriesTerm_measurable
    (k : ℕ) (x u v : ℝ) (n : ℕ) :
    Measurable (thetaMixedOneRightJetSeriesTerm k x u v n) := by
  by_cases hn : n = 0
  · subst n
    change Measurable (fun _ : ℝ => (0:ℝ))
    exact measurable_const
  · let p : ℝ := (n:ℝ)^2
    let d0 : ℝ := (p-1)/x
    have hm : Measurable (fun w : ℝ =>
        ((k:ℝ) * (-(p+w*x^2)) *
            (thetaWeightedGaussianRightMultiplier x p d0 u w)^(k-1) +
         (thetaWeightedGaussianRightMultiplier x p d0 u w)^k *
            thetaWeightedGaussianRightMultiplier x p d0 v w)) := by
      unfold thetaWeightedGaussianRightMultiplier
      fun_prop
    have hb : Measurable (fun w : ℝ =>
        thetaWeightedGaussianIntegrand x p d0 u v w) :=
      thetaWeightedGaussian_measurable x p d0 u v
    have hfull : Measurable (fun w : ℝ =>
        Real.exp (-(p-1)/x^2) *
          (((k:ℝ) * (-(p+w*x^2)) *
              (thetaWeightedGaussianRightMultiplier x p d0 u w)^(k-1) +
            (thetaWeightedGaussianRightMultiplier x p d0 u w)^k *
              thetaWeightedGaussianRightMultiplier x p d0 v w) *
            thetaWeightedGaussianIntegrand x p d0 u v w)) :=
      measurable_const.mul (hm.mul hb)
    change Measurable (fun w : ℝ =>
      if n = 0 then (0:ℝ) else
        Real.exp (-(p-1)/x^2) *
          (((k:ℝ) * (-(p+w*x^2)) *
              (thetaWeightedGaussianRightMultiplier x p d0 u w)^(k-1) +
            (thetaWeightedGaussianRightMultiplier x p d0 u w)^k *
              thetaWeightedGaussianRightMultiplier x p d0 v w) *
            thetaWeightedGaussianIntegrand x p d0 u v w))
    simpa only [if_neg hn] using hfull

/-- The individual mixed-jet w-integral is absolutely integrable
on the full positive half-line, uniformly on the common box. -/
theorem thetaMixedOneRightJetSeriesTerm_integrableOn
    (k : ℕ) (x u v : ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    IntegrableOn (thetaMixedOneRightJetSeriesTerm k x u v n)
      (Set.Ioi (0:ℝ)) volume := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hmajorant : Integrable
      (fun w : ℝ =>
        thetaMixedJetIndexFactor k x n * thetaMixedJetTailFactor k w) μ :=
    (thetaMixedJetTailFactor_integrableOn k).const_mul
      (thetaMixedJetIndexFactor k x n)
  have hmeas : AEStronglyMeasurable
      (thetaMixedOneRightJetSeriesTerm k x u v n) μ :=
    (thetaMixedOneRightJetSeriesTerm_measurable k x u v n).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤
        thetaMixedJetIndexFactor k x n * thetaMixedJetTailFactor k w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact thetaMixedOneRightJetSeriesTerm_norm_le_separable
      k x u v n w hx hx1 hu hv hw.le
  change Integrable (thetaMixedOneRightJetSeriesTerm k x u v n) μ
  exact hmajorant.mono' hmeas hbound

/-- The norm of each genuine integrated mixed jet is dominated
by one summable n-index factor times a constant w-integral. -/
theorem thetaMixedOneRightJetSeriesTerm_integral_norm_le
    (k : ℕ) (x u v : ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    ‖∫ w : ℝ, thetaMixedOneRightJetSeriesTerm k x u v n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))‖ ≤
      thetaMixedJetIndexFactor k x n *
        (∫ w : ℝ, thetaMixedJetTailFactor k w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hF : Integrable (thetaMixedOneRightJetSeriesTerm k x u v n) μ :=
    thetaMixedOneRightJetSeriesTerm_integrableOn
      k x u v n hx hx1 hu hv
  have hB : Integrable
      (fun w : ℝ =>
        thetaMixedJetIndexFactor k x n * thetaMixedJetTailFactor k w)
      μ :=
    (thetaMixedJetTailFactor_integrableOn k).const_mul
      (thetaMixedJetIndexFactor k x n)
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤
        thetaMixedJetIndexFactor k x n * thetaMixedJetTailFactor k w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact thetaMixedOneRightJetSeriesTerm_norm_le_separable
      k x u v n w hx hx1 hu hv hw.le
  calc
    ‖∫ w : ℝ, thetaMixedOneRightJetSeriesTerm k x u v n w ∂μ‖ ≤
      ∫ w : ℝ, ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℝ,
      thetaMixedJetIndexFactor k x n * thetaMixedJetTailFactor k w ∂μ :=
        integral_mono_ae hF.norm hB hbound
    _ = thetaMixedJetIndexFactor k x n *
        (∫ w : ℝ, thetaMixedJetTailFactor k w ∂μ) := by
      rw [integral_const_mul]

/-- A real Fubini interchange for all actual mixed Gaussian jets:
the infinite n-sum of w-integrals equals the w-integral of the
infinite n-sum. The majorant is explicit and verified in Lean. -/
theorem thetaMixedOneRightJetSeries_integral_hasSum
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    HasSum
      (fun n : ℕ =>
        ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, ∑' n : ℕ,
        thetaMixedOneRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let a : ℕ → ℝ := thetaMixedJetIndexFactor k x
  let b : ℝ → ℝ := thetaMixedJetTailFactor k
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hA : Summable a := thetaMixedJetIndexFactor_summable k x
  have hB : Integrable b μ := thetaMixedJetTailFactor_integrableOn k
  have hF : ∀ n : ℕ,
      AEStronglyMeasurable
        (thetaMixedOneRightJetSeriesTerm k x u v n) μ := by
    intro n
    exact (thetaMixedOneRightJetSeriesTerm_measurable k x u v n).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ∀ n : ℕ,
        ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤ a n*b w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw n
    exact thetaMixedOneRightJetSeriesTerm_norm_le_separable
      k x u v n w hx hx1 hu hv hw.le
  exact hasSum_integral_of_separable_bound μ
    (thetaMixedOneRightJetSeriesTerm k x u v) a b hA hB hF hbound

/-- Absolute summability of all integrated mixed theta jets. -/
theorem thetaMixedOneRightJetSeries_integrals_summable
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm k x u v n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
  (thetaMixedOneRightJetSeries_integral_hasSum k x u v hx hx1 hu hv).summable

end W5
