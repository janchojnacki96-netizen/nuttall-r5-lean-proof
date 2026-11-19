import W5.ThetaHigherRightJetSeriesDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# All ordinary iterated derivatives of the full transformed theta series

PR #50 proves that the full n-sum of integrated kth Gaussian jets
has derivative the sum of integrated (k+1)st jets throughout a
common open interval. In this module we iterate that result.

The subtle point is locality: the kth derivative of the original
series agrees with the kth-jet series only on the open patch, not
necessarily globally. We therefore use an eventual equality in
the neighborhood of each evaluation point before differentiating,
via Mathlib's `Filter.EventuallyEq.deriv_eq`.

For every k and v in (-x/8,x/8), this proves that the GENUINE
ordinary `iteratedDeriv k` of the infinite transformed theta
series equals both (a) the series of integrated kth Gaussian
jets and (b) the integral of the series of kth jets.

This is still the right-parameter transformed model. Identifying
the mixed partials of the original Nuttall normalized kernel and
proving the determinant sign are separate analytic steps.
-/

namespace W5
open MeasureTheory

/-- Genuine kth iterated right derivative of the full infinite
theta series of weighted, integrated Gaussians: the result is
the sum of their kth jet integrals, for any natural k. -/
theorem thetaHigherRightJet_integratedSeries_iteratedDeriv_eq
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8)
    (hv : v ∈ thetaGaussianSummableRightPatch x) :
    iteratedDeriv k
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x u z n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) v =
      ∑' n : ℕ,
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let s : Set ℝ := thetaGaussianSummableRightPatch x
  let F : ℝ → ℝ := fun z =>
    ∑' n : ℕ, ∫ w : ℝ,
      thetaHigherRightJetSeriesTerm 0 x u z n w ∂μ
  let G : ℕ → ℝ → ℝ := fun m z =>
    ∑' n : ℕ, ∫ w : ℝ,
      thetaHigherRightJetSeriesTerm m x u z n w ∂μ
  have hderiv (m : ℕ) (z : ℝ) (hz : z ∈ s) :
      HasDerivAt (G m) (G (m+1) z) z :=
    thetaHigherRightJet_integratedSeries_hasDerivAt
      m x u z hx hx1 hu hz
  have hall : ∀ m : ℕ, ∀ z : ℝ, z ∈ s →
      iteratedDeriv m F z = G m z := by
    intro m
    induction m with
    | zero =>
        intro z _
        simp only [iteratedDeriv_zero]
        rfl
    | succ m ih =>
        intro z hz
        rw [iteratedDeriv_succ]
        have heventual :
            (iteratedDeriv m F) =ᶠ[𝓝 z] (G m) := by
          filter_upwards [(thetaGaussianSummableRightPatch_isOpen x).mem_nhds hz]
            with y hy
          exact ih y hy
        rw [Filter.EventuallyEq.deriv_eq heventual]
        exact (hderiv m z hz).deriv
  exact hall k v hv

/-- The actual kth iterated derivative of the full transformed
theta series equals ONE Lebesgue integral over w>0 of the
pointwise infinite series of genuine kth theta jets. -/
theorem thetaHigherRightJet_integratedSeries_iteratedDeriv_eq_integral_tsum
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8)
    (hv : v ∈ thetaGaussianSummableRightPatch x) :
    iteratedDeriv k
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x u z n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) v =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaHigherRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  rw [thetaHigherRightJet_integratedSeries_iteratedDeriv_eq
    k x u v hx hx1 hu hv]
  exact (thetaHigherRightJetSeries_integral_hasSum
    k x u v hx hx1 hu
      (thetaGaussianSummableRightPatch_abs_le x v hv)).tsum_eq

end W5
