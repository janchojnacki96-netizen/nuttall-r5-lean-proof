import W5.ThetaAllOrdersTransformedSeriesBridge
import W5.ThetaWeightedGaussianMixedJets

/-!
# All left-variable derivatives of the genuine transformed theta series

The transformed Gaussian is symmetric in its two Taylor parameters.
Its pointwise symmetry was proved earlier; we transport it under the genuine
Lebesgue w-integral and infinite square-index sum. By transporting the
existing arbitrary-order right-derivative theorem through this exact
functional equality, we obtain arbitrary-order left derivatives with
an explicit sum/integral representation.

This proves one-variable differentiation in both coordinates, not
interchange of *mixed* derivatives, identification with the original
normalized Nuttall kernel, or any determinant sign.
-/

namespace W5
open MeasureTheory

/-- Arbitrary ordinary derivatives in the left coordinate, identified
with the already-proved right jets after exchanging the variables. -/
theorem thetaWeightedGaussian_iteratedDeriv_left
    (k : ℕ) (x p d0 u v w : ℝ) :
    iteratedDeriv k
        (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 z v w) u =
      thetaWeightedGaussianRightJet k x p d0 v u w := by
  have hswap :
      (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 z v w) =
      (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 v z w) := by
    funext z
    exact thetaWeightedGaussianIntegrand_swap x p d0 z v w
  rw [hswap]
  exact thetaWeightedGaussian_iteratedDeriv_right k x p d0 v u w

/-- Swapping the Taylor variables preserves each original integrated
transformed-theta summand, including the n=0 convention. -/
theorem thetaGaussianIntegratedSeriesTerm_swap
    (x u v : ℝ) (n : ℕ) :
    thetaGaussianIntegratedSeriesTerm x u n v =
      thetaGaussianIntegratedSeriesTerm x v n u := by
  by_cases hn : n = 0
  · simp [thetaGaussianIntegratedSeriesTerm, hn]
  · simp only [thetaGaussianIntegratedSeriesTerm, if_neg hn]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with w
    exact thetaWeightedGaussianIntegrand_swap
      x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v w

/-- Symmetry of the full transformed theta series is an equality of
actual infinite sums, not a symmetry postulate for a formal kernel. -/
theorem thetaGaussianIntegratedSeries_swap (x u v : ℝ) :
    (∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x u n v) =
      ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x v n u := by
  apply tsum_congr
  intro n
  exact thetaGaussianIntegratedSeriesTerm_swap x u v n

/-- The genuine kth left jet, obtained from the closed kth right
jet by exchanging the symmetric Taylor variables. -/
noncomputable def thetaHigherLeftJetSeriesTerm
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  thetaHigherRightJetSeriesTerm k x v u n w

/-- The complete transformed theta series has arbitrarily high
genuine left derivatives on the same common summability patch.
Its kth derivative is one Lebesgue integral of the full kth-jet
square-index series. No additional analytic interchange is assumed. -/
theorem thetaGaussianIntegratedSeries_iteratedDeriv_left_eq_integral_tsum
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : |v| ≤ x/8)
    (hu : u ∈ thetaGaussianSummableRightPatch x) :
    iteratedDeriv k
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n v) u =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaHigherLeftJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hswap :
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n v) =
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x v n z) := by
    funext z
    exact thetaGaussianIntegratedSeries_swap x z v
  rw [hswap]
  exact thetaGaussianIntegratedSeries_iteratedDeriv_eq_integral_tsum
    k x v u hx hx1 hv hu

end W5
