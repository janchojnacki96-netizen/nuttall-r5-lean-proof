import W5.ThetaHigherRightJetIteratedDerivative

/-!
# Identify the old transformed theta series with the all-orders jet family

PR #51 proves the exact iterated v-derivatives of the entire
integrated Gaussian series built from the *zeroth right jets*.
The earlier PR #38 introduced the same underlying series under
the name `thetaGaussianIntegratedSeriesTerm`.

This module proves that the two series are literally equal and
transports the all-orders iterated derivative theorem back to
the original transformed-series name.

This does not identify the transformed series with the original
normalized Nuttall kernel, nor establish any 5x5 determinant sign.
-/

namespace W5
open MeasureTheory

/-- At order zero the genuine Gaussian right jet is the original
un-differentiated, weighted theta summand, including index zero. -/
theorem thetaHigherRightJetSeriesTerm_zero_eq_base
    (x u v : ℝ) (n : ℕ) (w : ℝ) :
    thetaHigherRightJetSeriesTerm 0 x u v n w =
      thetaGaussianBaseSeriesTerm x u v n w := by
  by_cases hn : n = 0
  · subst n
    simp [thetaHigherRightJetSeriesTerm, thetaGaussianBaseSeriesTerm]
  · simp only [thetaHigherRightJetSeriesTerm,
      thetaGaussianBaseSeriesTerm, if_neg hn,
      thetaWeightedGaussianRightJet_zero]

/-- The nth original transformed theta w-integral is exactly
the integral of the kth-jet family at k=0. No analytic
interchange is used; it is a constant-multiplication identity. -/
theorem thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral
    (x u v : ℝ) (n : ℕ) :
    thetaGaussianIntegratedSeriesTerm x u n v =
      ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x u v n w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaGaussianIntegratedSeriesTerm,
      thetaHigherRightJetSeriesTerm]
  · simp only [thetaGaussianIntegratedSeriesTerm,
      thetaHigherRightJetSeriesTerm, if_neg hn,
      thetaWeightedGaussianRightJet_zero, integral_const_mul]

/-- The *old*, independently named full transformed theta series
now has exactly the iterated derivatives computed in PR #51,
for every natural order k on the common open parameter patch. -/
theorem thetaGaussianIntegratedSeries_iteratedDeriv_eq_integral_tsum
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8)
    (hv : v ∈ thetaGaussianSummableRightPatch x) :
    iteratedDeriv k
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x u n z) v =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaHigherRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hfunctions :
      (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x u n z) =
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x u z n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
    funext z
    apply tsum_congr
    intro n
    exact thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral x u z n
  rw [hfunctions]
  exact thetaHigherRightJet_integratedSeries_iteratedDeriv_eq_integral_tsum
    k x u v hx hx1 hu hv

end W5
