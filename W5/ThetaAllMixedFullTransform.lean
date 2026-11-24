import W5.ThetaAllMixedBaseSeries
import W5.ThetaOriginalKernelAllMixedJetsFromLocalEqOn

namespace W5
open MeasureTheory Filter
open scoped Topology

noncomputable def thetaFullMixedSeries (i j : ℕ) (x u v : ℝ) : ℝ :=
  (∑' n : ℕ, thetaBaseMixedTerm i j x u v n) -
    (x^2/4) * (∑' n : ℕ, ∫ w : ℝ, thetaAllMixedJetTerm x u v n w i j
      ∂(volume.restrict (Set.Ioi (0:ℝ))))

theorem thetaFullMixedSeries_hasDerivAt_right
    (j : ℕ) (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : v ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt (fun z => thetaFullMixedSeries 0 j x u z)
      (thetaFullMixedSeries 0 (j+1) x u v) v := by
  have h := (thetaBaseMixedSeries_hasDerivAt_right j x u v hx hx1 hu hv).sub
    ((thetaHigherRightJet_integratedSeries_hasDerivAt j x u v hx hx1 hu hv).const_mul (x^2/4))
  exact h

theorem thetaFullMixedSeries_hasDerivAt_left
    (i j : ℕ) (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : |v| ≤ x/8) (hu : u ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt (fun z => thetaFullMixedSeries i j x z v)
      (thetaFullMixedSeries (i+1) j x u v) u :=
  (thetaBaseMixedSeries_hasDerivAt_left i j x u v hx hx1 hv hu).sub
    ((thetaAllMixedJet_integratedSeries_hasDerivAt_left i j x u v hx hx1 hv hu).const_mul (x^2/4))

theorem thetaCertificateGaussianFullSeries_eq_fullMixed_zero
    (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    (∑' n : ℕ, thetaCertificateGaussianFullTerm x u v n) =
      thetaFullMixedSeries 0 0 x u v := by
  have hb := thetaBaseMixedTerm_summable 0 0 x u v hx hx1 hu hv
  have hc := (thetaAllMixedJet_integrals_summable 0 0 x u v hx hx1 hu hv).mul_left (x^2/4)
  calc
    _ = ∑' n : ℕ, (thetaBaseMixedTerm 0 0 x u v n -
          (x^2/4) * (∫ w : ℝ, thetaAllMixedJetTerm x u v n w 0 0
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
      apply tsum_congr
      intro n
      rw [thetaCertificateGaussianFullTerm_eq_base_sub_integrated,
        thetaCertificateGaussianBaseTerm_eq_zero_w,
        thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral]
      rfl
    _ = _ := by
      unfold thetaFullMixedSeries
      rw [← tsum_mul_left]
      exact (hb.hasSum.sub hc.hasSum).tsum_eq

theorem thetaCertificateGaussianFullSeries_right_jets
    (j : ℕ) (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : v ∈ thetaGaussianSummableRightPatch x) :
    iteratedDeriv j (fun z => ∑' n : ℕ, thetaCertificateGaussianFullTerm x u z n) v =
      thetaFullMixedSeries 0 j x u v := by
  let s := thetaGaussianSummableRightPatch x
  let F : ℝ → ℝ := fun z => ∑' n : ℕ, thetaCertificateGaussianFullTerm x u z n
  let G : ℕ → ℝ → ℝ := fun k z => thetaFullMixedSeries 0 k x u z
  have hall : ∀ k : ℕ, ∀ z ∈ s, iteratedDeriv k F z = G k z := by
    intro k
    induction k with
    | zero =>
        intro z hz
        simp only [iteratedDeriv_zero]
        exact thetaCertificateGaussianFullSeries_eq_fullMixed_zero x u z hx hx1 hu
          (thetaGaussianSummableRightPatch_abs_le x z hz)
    | succ k ih =>
        intro z hz
        rw [iteratedDeriv_succ]
        have heq : iteratedDeriv k F =ᶠ[𝓝 z] G k := by
          filter_upwards [(thetaGaussianSummableRightPatch_isOpen x).mem_nhds hz] with y hy
          exact ih y hy
        rw [Filter.EventuallyEq.deriv_eq heq]
        exact (thetaFullMixedSeries_hasDerivAt_right k x u z hx hx1 hu hz).deriv
  exact hall j v hv

theorem thetaCertificateGaussianFullSeries_mixed_jets
    (i j : ℕ) (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : u ∈ thetaGaussianSummableRightPatch x)
    (hv : v ∈ thetaGaussianSummableRightPatch x) :
    iteratedDeriv i (fun z => iteratedDeriv j
      (fun y => ∑' n : ℕ, thetaCertificateGaussianFullTerm x z y n) v) u =
      thetaFullMixedSeries i j x u v := by
  let s := thetaGaussianSummableRightPatch x
  let F : ℝ → ℝ := fun z => iteratedDeriv j
    (fun y => ∑' n : ℕ, thetaCertificateGaussianFullTerm x z y n) v
  let G : ℕ → ℝ → ℝ := fun k z => thetaFullMixedSeries k j x z v
  have hvabs := thetaGaussianSummableRightPatch_abs_le x v hv
  have hall : ∀ k : ℕ, ∀ z ∈ s, iteratedDeriv k F z = G k z := by
    intro k
    induction k with
    | zero =>
        intro z hz
        simp only [iteratedDeriv_zero]
        exact thetaCertificateGaussianFullSeries_right_jets j x z v hx hx1
          (thetaGaussianSummableRightPatch_abs_le x z hz) hv
    | succ k ih =>
        intro z hz
        rw [iteratedDeriv_succ]
        have heq : iteratedDeriv k F =ᶠ[𝓝 z] G k := by
          filter_upwards [(thetaGaussianSummableRightPatch_isOpen x).mem_nhds hz] with y hy
          exact ih y hy
        rw [Filter.EventuallyEq.deriv_eq heq]
        exact (thetaFullMixedSeries_hasDerivAt_left k j x z v hx hx1 hvabs hz).deriv
  exact hall i u hu

theorem thetaFullMixedSeries_origin_normalized
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (i j : Fin 5) :
    thetaFullMixedSeries i.val j.val x 0 0 /
      ((Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ)) =
      thetaCoefficient x i j := by
  let D : ℝ := (Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ)
  let B : ℕ → ℝ := thetaBaseMixedTerm i.val j.val x 0 0
  let C : ℕ → ℝ := fun n => ∫ w : ℝ, thetaAllMixedJetTerm x 0 0 n w i.val j.val
      ∂(volume.restrict (Set.Ioi (0:ℝ)))
  have hbase : (∑' n : ℕ, thetaCertificateBaseTerm x i j n) = (∑' n : ℕ, B n) / D := by
    calc
      _ = ∑' n : ℕ, B n / D := by
        apply tsum_congr
        intro n
        rw [thetaCertificateBaseTerm_eq_all_mixed_zero_w]
        unfold B D thetaBaseMixedTerm
        ring
      _ = _ := by simp only [div_eq_mul_inv, tsum_mul_right]
  have hcorr : (∑' n : ℕ, thetaCertificateCorrectionTerm x i j n) =
      (x^2/4) * ((∑' n : ℕ, C n) / D) := by
    calc
      _ = ∑' n : ℕ, (x^2/4) * (C n / D) := by
        apply tsum_congr
        intro n
        exact thetaCertificateCorrectionTerm_eq_all_mixed_integral x i j n
      _ = _ := by simp only [div_eq_mul_inv, tsum_mul_left, tsum_mul_right]
  rw [thetaCoefficient_all_eq_base_sub_correction x hx i j
    (thetaCertificateCorrectionTerm_all_summable x hx hx1 i j), hbase, hcorr]
  change ((∑' n : ℕ, B n) - (x^2/4) * (∑' n : ℕ, C n)) / D = _
  ring

theorem thetaTransformCorrect_allMixed : thetaTransformCorrect := by
  intro x hx hxB i j
  have hx1 : x ≤ 1 := by linarith
  have hz := thetaGaussianSummableRightPatch_zero_mem x hx
  rw [analyticCoeff_eq_thetaCertificateGaussianAnalyticCoeff x hx hxB]
  unfold thetaCertificateGaussianAnalyticCoeff
  rw [thetaCertificateGaussianFullSeries_mixed_jets i.val j.val x 0 0 hx hx1 hz hz]
  exact thetaFullMixedSeries_origin_normalized x hx hx1 i j

#print axioms thetaTransformCorrect_allMixed

end W5
