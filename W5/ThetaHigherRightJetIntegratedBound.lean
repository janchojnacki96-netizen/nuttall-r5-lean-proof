import W5.ThetaHigherRightJetFubini

/-!
# Uniform integrated majorants for the kth right theta Gaussian jet

The previous module establishes Fubini for the series of actual kth
pointwise Gaussian jets. Here we extract from its quantitative bound
an indexwise IntegrableOn theorem and a norm bound for the genuine
Lebesgue integral of *each* kth jet.

For each k, the resulting upper bound does not depend on u or v
inside the small parameter box. This is the needed integrability
input for parameter differentiation of the kth integrated jet.

No higher derivative / integral interchange is claimed yet.
-/

namespace W5
open MeasureTheory

/-- The index-dependent scalar part of the kth-jet majorant. -/
noncomputable def thetaHigherJetIndexFactor
    (k : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  ((1/x+2)^k * Real.exp (3/4)) *
    (((n:ℝ)^2+1)^(k+1) *
      Real.exp (-((47:ℝ)/64)*(n:ℝ)^2))

/-- The common integrable w-tail part of the kth-jet majorant. -/
noncomputable def thetaHigherJetTailFactor
    (k : ℕ) (w : ℝ) : ℝ :=
  ((w+1)^k*(w^2+w+1)) * Real.exp (-((1:ℝ)/4)*w)

/-- The norm of the actual kth theta right-jet summand is bounded
pointwise by the product, with the artificial zero index included. -/
theorem thetaHigherRightJetSeriesTerm_norm_le
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) (hw : 0 ≤ w) :
    ‖thetaHigherRightJetSeriesTerm k x u v n w‖ ≤
      thetaHigherJetIndexFactor k x n * thetaHigherJetTailFactor k w := by
  by_cases hn : n = 0
  · have hA : 0 ≤ thetaHigherJetIndexFactor k x n := by
      unfold thetaHigherJetIndexFactor
      positivity
    have hB : 0 ≤ thetaHigherJetTailFactor k w := by
      unfold thetaHigherJetTailFactor
      positivity
    simpa only [thetaHigherRightJetSeriesTerm, if_pos hn,
      norm_zero] using (mul_nonneg hA hB)
  · have hn1 : 1 ≤ n := by omega
    have hp : (1:ℝ) ≤ (n:ℝ)^2 := by
      have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      nlinarith
    have h := thetaGaussian_small_box_higher_right_jet_separable_bound
      k x ((n:ℝ)^2) u v w hx hx1 hp hw hu hv
    change ‖if n = 0 then (0:ℝ) else
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        thetaWeightedGaussianRightJet k x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w‖ ≤
      thetaHigherJetIndexFactor k x n * thetaHigherJetTailFactor k w
    rw [if_neg hn, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _)]
    simpa only [thetaHigherJetIndexFactor, thetaHigherJetTailFactor,
      mul_assoc] using h

/-- Each actual kth-jet integrand, including its index-zero case,
is Lebesgue-integrable on w>0. This is stronger than merely
knowing that its integral appears in a HasSum expression. -/
theorem thetaHigherRightJetSeriesTerm_integrableOn
    (k : ℕ) (x u v : ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    IntegrableOn (thetaHigherRightJetSeriesTerm k x u v n)
      (Set.Ioi (0:ℝ)) volume := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hB : Integrable
      (fun w : ℝ =>
        thetaHigherJetIndexFactor k x n * thetaHigherJetTailFactor k w)
      μ := by
    exact (thetaHigherJet_full_w_factor_integrableOn k).const_mul
      (thetaHigherJetIndexFactor k x n)
  have hmeas : AEStronglyMeasurable
      (thetaHigherRightJetSeriesTerm k x u v n) μ :=
    (thetaHigherRightJetSeriesTerm_measurable k x u v n).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ‖thetaHigherRightJetSeriesTerm k x u v n w‖ ≤
        thetaHigherJetIndexFactor k x n * thetaHigherJetTailFactor k w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact thetaHigherRightJetSeriesTerm_norm_le
      k x u v n w hx hx1 hu hv hw.le
  change Integrable (thetaHigherRightJetSeriesTerm k x u v n) μ
  exact hB.mono' hmeas hbound

/-- The true integral of the kth jet is uniformly bounded,
independently of u and v, by an explicitly summable index
factor times the integral of the common w-tail. -/
theorem thetaHigherRightJetSeriesTerm_integral_norm_le
    (k : ℕ) (x u v : ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    ‖∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u v n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))‖ ≤
      thetaHigherJetIndexFactor k x n *
        (∫ w : ℝ, thetaHigherJetTailFactor k w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hF : Integrable (thetaHigherRightJetSeriesTerm k x u v n) μ :=
    thetaHigherRightJetSeriesTerm_integrableOn
      k x u v n hx hx1 hu hv
  have hB : Integrable
      (fun w : ℝ =>
        thetaHigherJetIndexFactor k x n * thetaHigherJetTailFactor k w)
      μ := by
    exact (thetaHigherJet_full_w_factor_integrableOn k).const_mul
      (thetaHigherJetIndexFactor k x n)
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ‖thetaHigherRightJetSeriesTerm k x u v n w‖ ≤
        thetaHigherJetIndexFactor k x n * thetaHigherJetTailFactor k w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact thetaHigherRightJetSeriesTerm_norm_le
      k x u v n w hx hx1 hu hv hw.le
  calc
    ‖∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u v n w ∂μ‖ ≤
      ∫ w : ℝ, ‖thetaHigherRightJetSeriesTerm k x u v n w‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℝ,
      thetaHigherJetIndexFactor k x n * thetaHigherJetTailFactor k w ∂μ :=
        integral_mono_ae hF.norm hB hbound
    _ = thetaHigherJetIndexFactor k x n *
        (∫ w : ℝ, thetaHigherJetTailFactor k w ∂μ) := by
          rw [integral_const_mul]

/-- The index part of the integrated majorant is summable
for every fixed derivative order and every positive x. -/
theorem thetaHigherJetIndexFactor_summable (k : ℕ) (x : ℝ) :
    Summable (thetaHigherJetIndexFactor k x) := by
  change Summable (fun n : ℕ =>
    ((1/x+2)^k * Real.exp (3/4)) *
      (((n:ℝ)^2+1)^(k+1) *
        Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)))
  exact (thetaHigherJet_shifted_index_summable (k+1)).mul_left _

end W5
