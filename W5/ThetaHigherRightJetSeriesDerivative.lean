import W5.ThetaHigherRightJetIntegralDerivative
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiate the entire theta series of integrated right jets

For EVERY fixed k, previous modules prove that:
* the n-th integrated kth jet has derivative the n-th integrated
  (k+1)st jet at every v in the same open connected patch;
* these derivatives are uniformly dominated there by an explicitly
  summable n-dependent majorant;
* the series of kth integrated jets converges at the basepoint v=0.

Mathlib's `hasDerivAt_tsum_of_isPreconnected` therefore permits
passing ONE MORE v-derivative through the whole infinite n-series
at ANY order k. We also compose that result with the real Fubini
theorem for the (k+1)st jets to obtain a single integral formula.

This is a strong all-orders *right-parameter* result for the
transformed Gaussian model. It is not yet a statement about
mixed u,v derivatives, nor a proof of the Nuttall r=5 sign.
-/

namespace W5

open MeasureTheory

/-- For every k, the derivative of the entire infinite series
of kth integrated theta right jets is the series of integrals
of the (k+1)st jets. This holds on one shared open interval
(-x/8,x/8) and has no assumed convergence hypotheses. -/
theorem thetaHigherRightJet_integratedSeries_hasDerivAt
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8)
    (hv : v ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u z n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∑' n : ℕ,
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm (k+1) x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) v := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let s : Set ℝ := thetaGaussianSummableRightPatch x
  let f : ℕ → ℝ → ℝ := fun n z =>
    ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u z n w ∂μ
  let g : ℕ → ℝ → ℝ := fun n z =>
    ∫ w : ℝ, thetaHigherRightJetSeriesTerm (k+1) x u z n w ∂μ
  let a : ℕ → ℝ := fun n =>
    thetaHigherJetIndexFactor (k+1) x n *
      (∫ w : ℝ, thetaHigherJetTailFactor (k+1) w ∂μ)
  have hA : Summable a := by
    exact (thetaHigherJetIndexFactor_summable (k+1) x).mul_right
      (∫ w : ℝ, thetaHigherJetTailFactor (k+1) w ∂μ)
  have hopen : IsOpen s :=
    thetaGaussianSummableRightPatch_isOpen x
  have hconn : IsPreconnected s :=
    thetaGaussianSummableRightPatch_isPreconnected x
  have hzero : (0:ℝ) ∈ s :=
    thetaGaussianSummableRightPatch_zero_mem x hx
  have hdiff : ∀ n : ℕ, ∀ z : ℝ, z ∈ s →
      HasDerivAt (f n) (g n z) z := by
    intro n z hz
    exact thetaHigherRightJetSeries_integral_hasDerivAt_on_patch
      k x u n z hx hx1 hu hz
  have hbound : ∀ n : ℕ, ∀ z : ℝ, z ∈ s →
      ‖g n z‖ ≤ a n := by
    intro n z hz
    exact thetaHigherRightJetSeriesTerm_integral_norm_le
      (k+1) x u z n hx hx1 hu
        (thetaGaussianSummableRightPatch_abs_le x z hz)
  have hzabs : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hbase : Summable (fun n : ℕ => f n 0) :=
    thetaHigherRightJetSeries_integrals_summable
      k x u 0 hx hx1 hu hzabs
  change HasDerivAt (fun z : ℝ => ∑' n : ℕ, f n z)
    (∑' n : ℕ, g n v) v
  exact hasDerivAt_tsum_of_isPreconnected hA hopen hconn
    hdiff hbound hzero hbase hv

/-- Any kth integrated-jet sum has a derivative equal to ONE
integral of the full (k+1)st pointwise theta jet series. Both
the series differentiation and the Fubini exchange are proven,
rather than postulated as transformation assumptions. -/
theorem thetaHigherRightJet_integratedSeries_deriv_eq_integral_tsum
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8)
    (hv : v ∈ thetaGaussianSummableRightPatch x) :
    deriv
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u z n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))
      v =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaHigherRightJetSeriesTerm (k+1) x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  rw [(thetaHigherRightJet_integratedSeries_hasDerivAt
    k x u v hx hx1 hu hv).deriv]
  exact (thetaHigherRightJetSeries_integral_hasSum
    (k+1) x u v hx hx1 hu
      (thetaGaussianSummableRightPatch_abs_le x v hv)).tsum_eq

end W5
