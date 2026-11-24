import W5.ThetaAllMixedJetFubini
import W5.ThetaMixedJetIntegralAndSeriesDerivative

namespace W5
open MeasureTheory Filter
open scoped Topology

/-- Differentiating a single integrated kth right jet in u gives
the integral of the genuine (1,k) mixed jet on the common patch.
The interchange has an integrable bound independent of u. -/
theorem thetaAllMixedJet_integral_hasDerivAt_left_on_patch
    (i j : ℕ) (x v : ℝ) (n : ℕ) (u : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : |v| ≤ x/8)
    (hu : u ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt
      (fun z : ℝ =>
        ∫ w : ℝ, thetaAllMixedJetTerm x z v n w i j
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, thetaAllMixedJetTerm x u v n w (i+1) j
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) u := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let s : Set ℝ := thetaGaussianSummableRightPatch x
  let majorant : ℝ → ℝ := fun w =>
    thetaAllMixedJetIndexFactor (i+1) j x n * thetaHigherJetTailFactor (i+1+j) w
  have hbound :
      ∀ᵐ w : ℝ ∂μ,
        ∀ z ∈ s,
          ‖thetaAllMixedJetTerm x z v n w (i+1) j‖ ≤
            majorant w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    intro z hz
    exact thetaAllMixedJetTerm_norm_le_separable
      (i+1) j x z v n w hx hx1
        (thetaGaussianSummableRightPatch_abs_le x z hz) hv hw.le
  have hmajorant : Integrable majorant μ :=
    (thetaHigherJet_full_w_factor_integrableOn (i+1+j)).const_mul
      (thetaAllMixedJetIndexFactor (i+1) j x n)
  have hdiff :
      ∀ᵐ w : ℝ ∂μ,
        ∀ z ∈ s,
          HasDerivAt
            (fun y : ℝ => thetaAllMixedJetTerm x y v n w i j)
            (thetaAllMixedJetTerm x z v n w (i+1) j) z := by
    filter_upwards with w
    intro z _
    exact thetaAllMixedJetTerm_hasDerivAt_left x v n w i j z
  have hF_meas :
      ∀ᶠ z : ℝ in 𝓝 u,
        AEStronglyMeasurable
          (fun w : ℝ => thetaAllMixedJetTerm x z v n w i j) μ :=
    Filter.Eventually.of_forall (fun z =>
      (thetaAllMixedJetTerm_measurable x z v n i j).aestronglyMeasurable)
  have huabs : |u| ≤ x/8 :=
    thetaGaussianSummableRightPatch_abs_le x u hu
  have hF_int : Integrable
      (fun w => thetaAllMixedJetTerm x u v n w i j) μ :=
    thetaAllMixedJetTerm_integrableOn i j x u v n hx hx1 huabs hv
  have hF'_meas : AEStronglyMeasurable
      (fun w => thetaAllMixedJetTerm x u v n w (i+1) j) μ :=
    (thetaAllMixedJetTerm_measurable x u v n (i+1) j).aestronglyMeasurable
  have hnhds : s ∈ 𝓝 u :=
    (thetaGaussianSummableRightPatch_isOpen x).mem_nhds hu
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun z w => thetaAllMixedJetTerm x z v n w i j)
    (F' := fun z w => thetaAllMixedJetTerm x z v n w (i+1) j)
    (bound := majorant)
    (s := s)
    hnhds hF_meas hF_int hF'_meas hbound hmajorant hdiff).2

/-- Differentiating the FULL infinite n-sum of integrated kth
right jets in u: the derivative is the n-sum of genuine mixed
integrated jets. Both the single-term differentiation and
uniform summable derivative bound have been proved. -/
theorem thetaAllMixedJet_integratedSeries_hasDerivAt_left
    (i j : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : |v| ≤ x/8)
    (hu : u ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt
      (fun z : ℝ =>
        ∑' n : ℕ,
          ∫ w : ℝ, thetaAllMixedJetTerm x z v n w i j
            ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∑' n : ℕ,
        ∫ w : ℝ, thetaAllMixedJetTerm x u v n w (i+1) j
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) u := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let s : Set ℝ := thetaGaussianSummableRightPatch x
  let f : ℕ → ℝ → ℝ := fun n z =>
    ∫ w : ℝ, thetaAllMixedJetTerm x z v n w i j ∂μ
  let g : ℕ → ℝ → ℝ := fun n z =>
    ∫ w : ℝ, thetaAllMixedJetTerm x z v n w (i+1) j ∂μ
  let a : ℕ → ℝ := fun n =>
    thetaAllMixedJetIndexFactor (i+1) j x n *
      (∫ w : ℝ, thetaHigherJetTailFactor (i+1+j) w ∂μ)
  have hA : Summable a :=
    (thetaAllMixedJetIndexFactor_summable (i+1) j x).mul_right
      (∫ w : ℝ, thetaHigherJetTailFactor (i+1+j) w ∂μ)
  have hopen : IsOpen s := thetaGaussianSummableRightPatch_isOpen x
  have hconn : IsPreconnected s :=
    thetaGaussianSummableRightPatch_isPreconnected x
  have hzero : (0:ℝ) ∈ s :=
    thetaGaussianSummableRightPatch_zero_mem x hx
  have hdiff : ∀ n : ℕ, ∀ z : ℝ, z ∈ s →
      HasDerivAt (f n) (g n z) z := by
    intro n z hz
    exact thetaAllMixedJet_integral_hasDerivAt_left_on_patch
      i j x v n z hx hx1 hv hz
  have hbound : ∀ n : ℕ, ∀ z : ℝ, z ∈ s →
      ‖g n z‖ ≤ a n := by
    intro n z hz
    exact thetaAllMixedJetTerm_integral_norm_le
      (i+1) j x z v n hx hx1
        (thetaGaussianSummableRightPatch_abs_le x z hz) hv
  have h0abs : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hbase : Summable (fun n : ℕ => f n 0) :=
    thetaAllMixedJet_integrals_summable
      i j x 0 v hx hx1 h0abs hv
  change HasDerivAt (fun z : ℝ => ∑' n : ℕ, f n z)
    (∑' n : ℕ, g n u) u
  exact hasDerivAt_tsum_of_isPreconnected hA hopen hconn
    hdiff hbound hzero hbase hu

/-- All mixed derivatives of the genuine integrated weighted series. -/
theorem thetaAllMixedJet_integratedSeries_iteratedDeriv_eq
    (i j : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : v ∈ thetaGaussianSummableRightPatch x)
    (hu : u ∈ thetaGaussianSummableRightPatch x) :
    iteratedDeriv i
      (fun z : ℝ => iteratedDeriv j
        (fun y : ℝ => ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) v) u =
      ∑' n : ℕ, ∫ w : ℝ, thetaAllMixedJetTerm x u v n w i j
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let s := thetaGaussianSummableRightPatch x
  let F : ℝ → ℝ := fun z => iteratedDeriv j
    (fun y : ℝ => ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) v
  let G : ℕ → ℝ → ℝ := fun m z =>
    ∑' n : ℕ, ∫ w : ℝ, thetaAllMixedJetTerm x z v n w m j ∂μ
  have hvabs := thetaGaussianSummableRightPatch_abs_le x v hv
  have hderiv (m : ℕ) (z : ℝ) (hz : z ∈ s) :
      HasDerivAt (G m) (G (m+1) z) z :=
    thetaAllMixedJet_integratedSeries_hasDerivAt_left m j x z v hx hx1 hvabs hz
  have hall : ∀ m : ℕ, ∀ z : ℝ, z ∈ s →
      iteratedDeriv m F z = G m z := by
    intro m
    induction m with
    | zero =>
        intro z hz
        simp only [iteratedDeriv_zero]
        have hfun :
            (fun y : ℝ => ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) =
            (fun y : ℝ => ∑' n : ℕ,
              ∫ w : ℝ, thetaHigherRightJetSeriesTerm 0 x z y n w ∂μ) := by
          funext y
          apply tsum_congr
          intro n
          exact thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral x z y n
        change iteratedDeriv j
          (fun y : ℝ => ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) v = G 0 z
        rw [hfun]
        exact thetaHigherRightJet_integratedSeries_iteratedDeriv_eq
          j x z v hx hx1 (thetaGaussianSummableRightPatch_abs_le x z hz) hv
    | succ m ih =>
        intro z hz
        rw [iteratedDeriv_succ]
        have heventual : (iteratedDeriv m F) =ᶠ[𝓝 z] (G m) := by
          filter_upwards [(thetaGaussianSummableRightPatch_isOpen x).mem_nhds hz] with y hy
          exact ih y hy
        rw [Filter.EventuallyEq.deriv_eq heventual]
        exact (hderiv m z hz).deriv
  exact hall i u hu

end W5
