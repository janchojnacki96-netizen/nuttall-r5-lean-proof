import W5.ThetaMathlibTwoVariableOrderEightTsum
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Apply Mathlib's LOCAL Fréchet-derivative series theorem to actual theta

Mathlib's global `iteratedFDeriv_tsum_apply` (tested in the
parent experiment) needs derivative bounds on ALL of ℝ².
The true theta Gaussian exhibits growth away from the Taylor
origin, so our existing bounds are only local.

Mathlib ALSO contains
  `hasFDerivAt_tsum_of_isPreconnected`,
which needs bounds only on one open preconnected parameter patch.

A metric ball in the 2-parameter space Fin 2 → ℝ is both open
and preconnected. The integrated theta series is already known
to converge at its origin from our genuine k=0 Fubini theorem.

Therefore we discharge ALL topology and basepoint summability
obligations and leave only:
  * each n-th integrated theta term's true two-variable FDeriv;
  * a summable majorant uniform ON THE BALL.

No global cutoff is required for this first multivariate
differentiation step. Iterating it through total order eight
still needs higher derivative majorants and compatibility
between ordinary mixed derivatives and Fréchet jets.

No sign claim or unproved numerical assumption is introduced.
-/

namespace W5
open MeasureTheory

/-- Genuine two-parameter Fréchet differentiation of the ENTIRE
infinite theta series on a local ball, assuming precisely the
remaining local differentiated-term estimates.

The series basepoint summability is proven, rather than assumed,
using the already verified k=0 Gaussian Fubini estimates. -/
theorem thetaIntegratedSeries_hasFDerivAt_twoVariable_on_ball
    (x radius : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hr : 0 < radius)
    (jet : ℕ → (Fin 2 → ℝ) → ((Fin 2 → ℝ) →L[ℝ] ℝ))
    (majorant : ℕ → ℝ)
    (hsummable : Summable majorant)
    (hjet :
      ∀ (n : ℕ) (z : Fin 2 → ℝ),
        z ∈ Metric.ball (0 : Fin 2 → ℝ) radius →
          HasFDerivAt
            (thetaIntegratedSeriesTermTwoVariable x n)
            (jet n z) z)
    (hbound :
      ∀ (n : ℕ) (z : Fin 2 → ℝ),
        z ∈ Metric.ball (0 : Fin 2 → ℝ) radius →
          ‖jet n z‖ ≤ majorant n)
    (z : Fin 2 → ℝ)
    (hz : z ∈ Metric.ball (0 : Fin 2 → ℝ) radius) :
    HasFDerivAt
      (fun y : Fin 2 → ℝ =>
        ∑' n : ℕ, thetaIntegratedSeriesTermTwoVariable x n y)
      (∑' n : ℕ, jet n z) z := by
  have hzero : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hbasejets :
      Summable (fun n : ℕ =>
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
    thetaHigherRightJetSeries_integrals_summable
      0 x 0 0 hx hx1 hzero hzero
  have hbase :
      Summable (fun n : ℕ =>
        thetaIntegratedSeriesTermTwoVariable x n (0 : Fin 2 → ℝ)) := by
    have heq :
        (fun n : ℕ =>
          thetaIntegratedSeriesTermTwoVariable x n (0 : Fin 2 → ℝ)) =
        (fun n : ℕ =>
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
      funext n
      simpa [thetaIntegratedSeriesTermTwoVariable] using
        (thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral x 0 0 n)
    rw [heq]
    exact hbasejets
  have hopen : IsOpen (Metric.ball (0 : Fin 2 → ℝ) radius) :=
    Metric.isOpen_ball
  have hconnected : IsPreconnected
      (Metric.ball (0 : Fin 2 → ℝ) radius) :=
    Metric.isPreconnected_ball
  have horigin :
      (0 : Fin 2 → ℝ) ∈ Metric.ball (0 : Fin 2 → ℝ) radius :=
    Metric.mem_ball_self hr
  exact hasFDerivAt_tsum_of_isPreconnected
    hsummable hopen hconnected hjet hbound horigin hbase hz

end W5
