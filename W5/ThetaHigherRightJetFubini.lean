import W5.ThetaHigherJetShiftedPolynomialTails
import W5.ThetaSeparableFubini

/-!
# Fubini for every fixed-order right jet of the genuine theta Gaussian

PRs #41-#46 prove (i) the exact kth v-derivative of a weighted theta
Gaussian, (ii) a fully separable Gaussian/exponential majorant, and
(iii) summability of the n-factor and integrability of the w-factor.

Here we apply the existing Mathlib dominated-convergence Fubini lemma
to the actual kth jet, with the outer exp(-(n²-1)/x²) factor and
the natural index n=0 set to zero.

This is an unconditional sum/integral exchange for the series of
pointwise kth jets, uniformly on the small closed parameter box.
It does NOT on its own assert that an integral or sum of the kth
jets is the kth derivative of the original transformed theta series.
Those further derivative-interchange steps remain explicit goals.
-/

namespace W5

open MeasureTheory

/-- The genuine weighted Gaussian right jet is measurable in w
for any real parameters, without requiring positivity assumptions. -/
theorem thetaWeightedGaussianRightJet_measurable
    (k : ℕ) (x p d0 u v : ℝ) :
    Measurable (fun w : ℝ =>
      thetaWeightedGaussianRightJet k x p d0 u v w) := by
  have hm : Measurable (fun w : ℝ =>
      ((-d0-p*u)-w*x*(1+x*u))^k) := by
    fun_prop
  have hf := thetaWeightedGaussian_measurable x p d0 u v
  change Measurable (fun w : ℝ =>
    ((-d0-p*u)-w*x*(1+x*u))^k *
      thetaWeightedGaussianIntegrand x p d0 u v w)
  convert hm.mul hf using 1

/-- The actual kth right jet with n²-substitution and exterior
Gaussian factor. The index zero vanishes, matching the original
theta series and avoiding division by zero in n². -/
noncomputable def thetaHigherRightJetSeriesTerm
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  if n = 0 then 0 else
    Real.exp (-((n:ℝ)^2-1)/x^2) *
      thetaWeightedGaussianRightJet k x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) u v w

theorem thetaHigherRightJetSeriesTerm_measurable
    (k : ℕ) (x u v : ℝ) (n : ℕ) :
    Measurable (thetaHigherRightJetSeriesTerm k x u v n) := by
  by_cases hn : n = 0
  · subst n
    change Measurable (fun _ : ℝ => (0:ℝ))
    exact measurable_const
  · have hm : Measurable (fun w : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightJet k x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w) :=
      measurable_const.mul
        (thetaWeightedGaussianRightJet_measurable k
          x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v)
    change Measurable (fun w : ℝ =>
      if n = 0 then (0:ℝ) else
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightJet k x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w)
    simpa only [if_neg hn] using hm

/-- For every fixed derivative order k, a single explicit
separable majorant makes the series of actual kth jets
interchangeable with the Lebesgue integral over w>0. -/
theorem thetaHigherRightJetSeries_integral_hasSum
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    HasSum
      (fun n : ℕ =>
        ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, ∑' n : ℕ,
        thetaHigherRightJetSeriesTerm k x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let C : ℝ := (1/x+2)^k * Real.exp (3/4)
  let a : ℕ → ℝ := fun n =>
    C * (((n:ℝ)^2+1)^(k+1) *
      Real.exp (-((47:ℝ)/64)*(n:ℝ)^2))
  let b : ℝ → ℝ := fun w =>
    ((w+1)^k*(w^2+w+1))*Real.exp (-((1:ℝ)/4)*w)
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hA : Summable a := by
    change Summable (fun n : ℕ =>
      C * (((n:ℝ)^2+1)^(k+1) *
        Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)))
    exact (thetaHigherJet_shifted_index_summable (k+1)).mul_left C
  have hB : Integrable b μ := by
    change IntegrableOn b (Set.Ioi (0:ℝ)) volume
    exact thetaHigherJet_full_w_factor_integrableOn k
  have hF : ∀ n : ℕ,
      AEStronglyMeasurable (thetaHigherRightJetSeriesTerm k x u v n) μ := by
    intro n
    exact (thetaHigherRightJetSeriesTerm_measurable k x u v n).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ∀ n : ℕ, ‖thetaHigherRightJetSeriesTerm k x u v n w‖ ≤ a n*b w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw n
    have hw0 : 0 ≤ w := hw.le
    by_cases hn : n = 0
    · have ha : 0 ≤ a n := by
        dsimp [a, C]
        have hxC : 0 ≤ 1/x+2 := by positivity
        positivity
      have hb : 0 ≤ b w := by
        dsimp [b]
        positivity
      simpa only [thetaHigherRightJetSeriesTerm, if_pos hn,
        norm_zero] using (mul_nonneg ha hb)
    · have hn1 : 1 ≤ n := by omega
      have hp : (1:ℝ) ≤ (n:ℝ)^2 := by
        have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        nlinarith
      have h := thetaGaussian_small_box_higher_right_jet_separable_bound
        k x ((n:ℝ)^2) u v w hx hx1 hp hw0 hu hv
      have heq : a n*b w =
          C *
            (((n:ℝ)^2+1)^(k+1) *
              Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) *
              (((w+1)^k*(w^2+w+1)) *
                Real.exp (-((1:ℝ)/4)*w)) := by
        dsimp [a, b]
      rw [heq]
      change ‖if n = 0 then (0:ℝ) else
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianRightJet k x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w‖ ≤
          C *
            (((n:ℝ)^2+1)^(k+1) *
              Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) *
              (((w+1)^k*(w^2+w+1)) *
                Real.exp (-((1:ℝ)/4)*w))
      rw [if_neg hn, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.exp_nonneg _)]
      simpa only [C, mul_assoc] using h
  exact hasSum_integral_of_separable_bound μ
    (thetaHigherRightJetSeriesTerm k x u v) a b
    hA hB hF hbound

/-- The integrated kth right jets form an absolutely convergent
series, for any fixed k and for all parameters in the small box. -/
theorem thetaHigherRightJetSeries_integrals_summable
    (k : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaHigherRightJetSeriesTerm k x u v n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
  (thetaHigherRightJetSeries_integral_hasSum k x u v hx hx1 hu hv).summable

end W5
