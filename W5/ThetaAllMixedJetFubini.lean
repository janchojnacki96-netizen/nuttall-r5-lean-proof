import W5.ThetaAllMixedJetEnvelope
import W5.ThetaSeparableFubini

namespace W5
open MeasureTheory

/-- The individual mixed-jet w-integral is absolutely integrable
on the full positive half-line, uniformly on the common box. -/
theorem thetaAllMixedJetTerm_integrableOn
    (i j : ℕ) (x u v : ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    IntegrableOn ((fun w => thetaAllMixedJetTerm x u v n w i j))
      (Set.Ioi (0:ℝ)) volume := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hmajorant : Integrable
      (fun w : ℝ =>
        thetaAllMixedJetIndexFactor i j x n * thetaHigherJetTailFactor (i+j) w) μ :=
    (thetaHigherJet_full_w_factor_integrableOn (i+j)).const_mul
      (thetaAllMixedJetIndexFactor i j x n)
  have hmeas : AEStronglyMeasurable
      ((fun w => thetaAllMixedJetTerm x u v n w i j)) μ :=
    (thetaAllMixedJetTerm_measurable x u v n i j).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ‖thetaAllMixedJetTerm x u v n w i j‖ ≤
        thetaAllMixedJetIndexFactor i j x n * thetaHigherJetTailFactor (i+j) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact thetaAllMixedJetTerm_norm_le_separable
      i j x u v n w hx hx1 hu hv hw.le
  change Integrable ((fun w => thetaAllMixedJetTerm x u v n w i j)) μ
  exact hmajorant.mono' hmeas hbound

/-- The norm of each genuine integrated mixed jet is dominated
by one summable n-index factor times a constant w-integral. -/
theorem thetaAllMixedJetTerm_integral_norm_le
    (i j : ℕ) (x u v : ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    ‖∫ w : ℝ, thetaAllMixedJetTerm x u v n w i j
        ∂(volume.restrict (Set.Ioi (0:ℝ)))‖ ≤
      thetaAllMixedJetIndexFactor i j x n *
        (∫ w : ℝ, thetaHigherJetTailFactor (i+j) w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hF : Integrable ((fun w => thetaAllMixedJetTerm x u v n w i j)) μ :=
    thetaAllMixedJetTerm_integrableOn
      i j x u v n hx hx1 hu hv
  have hB : Integrable
      (fun w : ℝ =>
        thetaAllMixedJetIndexFactor i j x n * thetaHigherJetTailFactor (i+j) w)
      μ :=
    (thetaHigherJet_full_w_factor_integrableOn (i+j)).const_mul
      (thetaAllMixedJetIndexFactor i j x n)
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ‖thetaAllMixedJetTerm x u v n w i j‖ ≤
        thetaAllMixedJetIndexFactor i j x n * thetaHigherJetTailFactor (i+j) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact thetaAllMixedJetTerm_norm_le_separable
      i j x u v n w hx hx1 hu hv hw.le
  calc
    ‖∫ w : ℝ, thetaAllMixedJetTerm x u v n w i j ∂μ‖ ≤
      ∫ w : ℝ, ‖thetaAllMixedJetTerm x u v n w i j‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℝ,
      thetaAllMixedJetIndexFactor i j x n * thetaHigherJetTailFactor (i+j) w ∂μ :=
        integral_mono_ae hF.norm hB hbound
    _ = thetaAllMixedJetIndexFactor i j x n *
        (∫ w : ℝ, thetaHigherJetTailFactor (i+j) w ∂μ) := by
      rw [integral_const_mul]

/-- A real Fubini interchange for all actual mixed Gaussian jets:
the infinite n-sum of w-integrals equals the w-integral of the
infinite n-sum. The majorant is explicit and verified in Lean. -/
theorem thetaAllMixedJet_integral_hasSum
    (i j : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    HasSum
      (fun n : ℕ =>
        ∫ w : ℝ, thetaAllMixedJetTerm x u v n w i j
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, ∑' n : ℕ,
        thetaAllMixedJetTerm x u v n w i j
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let a : ℕ → ℝ := thetaAllMixedJetIndexFactor i j x
  let b : ℝ → ℝ := thetaHigherJetTailFactor (i+j)
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hA : Summable a := thetaAllMixedJetIndexFactor_summable i j x
  have hB : Integrable b μ := thetaHigherJet_full_w_factor_integrableOn (i+j)
  have hF : ∀ n : ℕ,
      AEStronglyMeasurable
        ((fun w => thetaAllMixedJetTerm x u v n w i j)) μ := by
    intro n
    exact (thetaAllMixedJetTerm_measurable x u v n i j).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ∀ n : ℕ,
        ‖thetaAllMixedJetTerm x u v n w i j‖ ≤ a n*b w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw n
    exact thetaAllMixedJetTerm_norm_le_separable
      i j x u v n w hx hx1 hu hv hw.le
  exact hasSum_integral_of_separable_bound μ
    (fun n w => thetaAllMixedJetTerm x u v n w i j) a b hA hB hF hbound

/-- Absolute summability of all integrated mixed theta jets. -/
theorem thetaAllMixedJet_integrals_summable
    (i j : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaAllMixedJetTerm x u v n w i j
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
  (thetaAllMixedJet_integral_hasSum i j x u v hx hx1 hu hv).summable

end W5
