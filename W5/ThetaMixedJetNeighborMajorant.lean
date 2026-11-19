import W5.ThetaMixedRightJetSeriesDerivative
import W5.ThetaHigherRightJetIntegratedBound

/-!
# Gaussian bounds for mixed left/right theta jets

The genuine one-left/k-right square-index jet is an explicit sum of
TWO already controlled right jets, of orders k-1 and k. This yields
an exact algebraic decomposition and a quantitative pointwise bound
through the previously verified all-order Gaussian majorants.

The bound is uniform on the same small two-parameter box as the
right-jet estimates, with square-index Gaussian decay and w-exponential
decay retained. The next step is to separate and integrate its extra
(p+w) multiplier.

No sum/integral differentiation interchange, original-kernel
identification, or Wronskian sign is claimed here.
-/

namespace W5

/-- The mixed jet is a linear combination of TWO successive
right jets. This identity holds also for k=0 and n=0. -/
theorem thetaMixedOneRightJetSeriesTerm_eq_neighbors
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ) :
    thetaMixedOneRightJetSeriesTerm k x u v n w =
      (k : ℝ) * (-( (n:ℝ)^2 + w*x^2)) *
        thetaHigherRightJetSeriesTerm (k-1) x u v n w +
      thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) v w *
        thetaHigherRightJetSeriesTerm k x u v n w := by
  by_cases hn : n = 0
  · subst n
    simp [thetaMixedOneRightJetSeriesTerm,
      thetaHigherRightJetSeriesTerm]
  · simp only [thetaMixedOneRightJetSeriesTerm,
      thetaHigherRightJetSeriesTerm, if_neg hn,
      thetaWeightedGaussianRightJet]
    ring

/-- Elementary norm estimate: a genuine mixed jet is bounded by
two neighboring genuine right-jet norms. No parameter assumptions. -/
theorem thetaMixedOneRightJetSeriesTerm_norm_le_neighbors
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ) :
    ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤
      (k : ℝ) * |(n:ℝ)^2+w*x^2| *
        ‖thetaHigherRightJetSeriesTerm (k-1) x u v n w‖ +
      |thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) v w| *
        ‖thetaHigherRightJetSeriesTerm k x u v n w‖ := by
  rw [thetaMixedOneRightJetSeriesTerm_eq_neighbors]
  calc
    ‖(k : ℝ) * (-( (n:ℝ)^2 + w*x^2)) *
          thetaHigherRightJetSeriesTerm (k-1) x u v n w +
        thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) v w *
          thetaHigherRightJetSeriesTerm k x u v n w‖ ≤
      ‖(k : ℝ) * (-( (n:ℝ)^2 + w*x^2)) *
          thetaHigherRightJetSeriesTerm (k-1) x u v n w‖ +
      ‖thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) v w *
        thetaHigherRightJetSeriesTerm k x u v n w‖ := norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg k)]
      ring

/-- Uniform bound for any mixed one-left/k-right theta Gaussian jet.
The two Gaussian factors come directly from already verified jet
majorants; only the harmless polynomial p+w is added. -/
theorem thetaMixedOneRightJetSeriesTerm_norm_le_two_gaussian_factors
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) (hw : 0 ≤ w) :
    ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤
      (k:ℝ) * (((n:ℝ)^2)+w) *
        (thetaHigherJetIndexFactor (k-1) x n *
          thetaHigherJetTailFactor (k-1) w) +
      (1/x+2) * (((n:ℝ)^2)+w) *
        (thetaHigherJetIndexFactor k x n *
          thetaHigherJetTailFactor k w) := by
  by_cases hn : n = 0
  · subst n
    have hI : 0 ≤ thetaHigherJetIndexFactor (k-1) x 0 := by
      unfold thetaHigherJetIndexFactor
      positivity
    have hJ : 0 ≤ thetaHigherJetIndexFactor k x 0 := by
      unfold thetaHigherJetIndexFactor
      positivity
    have hT : 0 ≤ thetaHigherJetTailFactor (k-1) w := by
      unfold thetaHigherJetTailFactor
      positivity
    have hU : 0 ≤ thetaHigherJetTailFactor k w := by
      unfold thetaHigherJetTailFactor
      positivity
    have hc : 0 ≤ 1/x+2 := by positivity
    have hfirst : 0 ≤ (k:ℝ) * ((0:ℝ)+w) *
        (thetaHigherJetIndexFactor (k-1) x 0 *
          thetaHigherJetTailFactor (k-1) w) := by positivity
    have hsecond : 0 ≤ (1/x+2) * ((0:ℝ)+w) *
        (thetaHigherJetIndexFactor k x 0 *
          thetaHigherJetTailFactor k w) := by positivity
    simpa [thetaMixedOneRightJetSeriesTerm] using add_nonneg hfirst hsecond
  · let p : ℝ := (n:ℝ)^2
    have hn1 : 1 ≤ n := by omega
    have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have hp : 1 ≤ p := by
      dsimp [p]
      nlinarith
    have hp0 : 0 ≤ p := by linarith
    have hx2 : x^2 ≤ 1 := by
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
    have hq : |p+w*x^2| ≤ p+w := by
      have hwx : 0 ≤ w*x^2 := mul_nonneg hw (sq_nonneg x)
      rw [abs_of_nonneg (add_nonneg hp0 hwx)]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hx2)]
    have hmabs :
        |thetaWeightedGaussianRightMultiplier x p ((p-1)/x) v w| ≤
          |(p-1)/x+p*v| + w*|x*(1+x*v)| := by
      simpa only [thetaWeightedGaussianRightMultiplier] using
        thetaGaussian_right_multiplier_abs_le x p ((p-1)/x) v w hw
    have hm :
        |thetaWeightedGaussianRightMultiplier x p ((p-1)/x) v w| ≤
          (1/x+2)*(p+w) :=
      hmabs.trans (thetaGaussian_small_box_right_multiplier_le
        x p v w hx hx1 hp hw hv)
    have hprev := thetaHigherRightJetSeriesTerm_norm_le
      (k-1) x u v n w hx hx1 hu hv hw
    have hnow := thetaHigherRightJetSeriesTerm_norm_le
      k x u v n w hx hx1 hu hv hw
    have hqpos : 0 ≤ p+w := add_nonneg hp0 hw
    have hC : 0 ≤ 1/x+2 := by positivity
    have hfirst :
        (k:ℝ) * |p+w*x^2| *
          ‖thetaHigherRightJetSeriesTerm (k-1) x u v n w‖ ≤
        (k:ℝ) * (p+w) *
          (thetaHigherJetIndexFactor (k-1) x n *
            thetaHigherJetTailFactor (k-1) w) := by
      gcongr
    have hsecond :
        |thetaWeightedGaussianRightMultiplier x p ((p-1)/x) v w| *
          ‖thetaHigherRightJetSeriesTerm k x u v n w‖ ≤
        (1/x+2)*(p+w) *
          (thetaHigherJetIndexFactor k x n *
            thetaHigherJetTailFactor k w) := by
      gcongr
    have hmain := thetaMixedOneRightJetSeriesTerm_norm_le_neighbors
      k x u v n w
    change ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤
      (k:ℝ)*|p+w*x^2|*
        ‖thetaHigherRightJetSeriesTerm (k-1) x u v n w‖ +
      |thetaWeightedGaussianRightMultiplier x p ((p-1)/x) v w| *
        ‖thetaHigherRightJetSeriesTerm k x u v n w‖ at hmain
    exact hmain.trans (add_le_add hfirst hsecond)

end W5
