import W5.ThetaGaussianFullFirstDerivativeFubini

/-!
# Differentiability of the entire transformed theta series on a common patch

PR #38 proves that the full transformed, integrated theta n-series
is differentiable at v=0.  The hypotheses already established in the
preceding modules actually imply the corresponding result at *every*
v in the same connected open interval (-x/8, x/8).

We expose that stronger conclusion, without conflating it with
higher-order differentiability or the Nuttall r=5 sign problem.
-/

namespace W5
open MeasureTheory

/-- First derivative of the full infinite series of integrated
weighted Gaussian theta terms at every parameter v in the shared
small open box.  The right side is the sum of genuine derivatives of
the integrated terms and has an index-summable uniform majorant. -/
theorem thetaGaussianIntegratedSeries_hasDerivAt_on_summablePatch
    (x u : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8)
    (v0 : ℝ) (hv0 : v0 ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt
      (fun v : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x u n v)
      (∑' n : ℕ, thetaGaussianIntegratedSeriesDerivative x u n v0)
      v0 := by
  let patch : Set ℝ := thetaGaussianSummableRightPatch x
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  let C : ℝ := Real.exp (3/4)*(1/x+2)
  let a : ℕ → ℝ := fun n =>
    C * (∫ w : ℝ, thetaGaussianProductMajorant n w ∂μ)
  have hA : Summable a :=
    thetaGaussian_integrated_deriv_majorant_summable x
  have hopen : IsOpen patch :=
    thetaGaussianSummableRightPatch_isOpen x
  have hconn : IsPreconnected patch :=
    thetaGaussianSummableRightPatch_isPreconnected x
  have hzero : (0:ℝ) ∈ patch :=
    thetaGaussianSummableRightPatch_zero_mem x hx
  have hlocal := thetaGaussian_small_box_inside_local_patch x u hx hx1 hu
  have hdiff :
      ∀ n : ℕ, ∀ v : ℝ, v ∈ patch →
        HasDerivAt
          (thetaGaussianIntegratedSeriesTerm x u n)
          (thetaGaussianIntegratedSeriesDerivative x u n v) v := by
    intro n v hv
    by_cases hn : n = 0
    · subst n
      change HasDerivAt (fun _ : ℝ => (0:ℝ)) (0:ℝ) v
      exact hasDerivAt_const v 0
    · have hn1 : 1 ≤ n := by omega
      have hsmallpatch : v ∈ thetaGaussianSummableRightPatch x := hv
      have hvpatch :
          v ∈ thetaGaussianRightPatch x :=
        thetaGaussianSummableRightPatch_subset_rightPatch x hx hx1 hv
      have hsingle :=
        thetaGaussian_nonzero_index_integral_hasDerivAt_on_rightPatch
          x n hn1 u v hlocal.1 hlocal.2 hvpatch
      change HasDerivAt
        (fun z : ℝ =>
          if n = 0 then (0:ℝ) else
            Real.exp (-((n:ℝ)^2-1)/x^2) *
              (∫ w : ℝ,
                thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
                  (((n:ℝ)^2-1)/x) u z w ∂μ))
        (if n = 0 then (0:ℝ) else
          Real.exp (-((n:ℝ)^2-1)/x^2) *
            (∫ w : ℝ,
              thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
                (((n:ℝ)^2-1)/x) u v w ∂μ)) v
      simpa only [if_neg hn] using hsingle
  have hM0 :
      0 ≤ ∫ w : ℝ, thetaGaussianProductMajorant 0 w ∂μ := by
    apply integral_nonneg
    intro w
    have hpoly : 0 ≤ w^2+w+1 := by
      nlinarith [sq_nonneg (w+1/2)]
    dsimp [thetaGaussianProductMajorant]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have hi : 0 ≤ 1/x := by positivity
    positivity
  have hbound :
      ∀ n : ℕ, ∀ v : ℝ, v ∈ patch →
        ‖thetaGaussianIntegratedSeriesDerivative x u n v‖ ≤ a n := by
    intro n v hv
    by_cases hn : n = 0
    · subst n
      have h := mul_nonneg hC hM0
      change ‖(0:ℝ)‖ ≤ C *
        (∫ w : ℝ, thetaGaussianProductMajorant 0 w ∂μ)
      simpa using h
    · have hn1 : 1 ≤ n := by omega
      have hb :=
        thetaGaussian_nonzero_index_integrated_deriv_bound_on_summablePatch
          x hx hx1 n hn1 u v hu hv
      change ‖if n = 0 then (0:ℝ) else
          Real.exp (-((n:ℝ)^2-1)/x^2) *
            (∫ w : ℝ,
              thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
                (((n:ℝ)^2-1)/x) u v w ∂μ)‖ ≤
        C * (∫ w : ℝ, thetaGaussianProductMajorant n w ∂μ)
      simpa only [if_neg hn] using hb
  have hzabs : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hbase_integrals :=
    thetaGaussianBaseSeries_integrals_summable x u 0 hx hx1 hu hzabs
  have hbaseeq :
      (fun n : ℕ => thetaGaussianIntegratedSeriesTerm x u n 0) =
      (fun n : ℕ =>
        ∫ w : ℝ, thetaGaussianBaseSeriesTerm x u 0 n w ∂μ) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [thetaGaussianIntegratedSeriesTerm, thetaGaussianBaseSeriesTerm]
    · change (if n = 0 then (0:ℝ) else
          Real.exp (-((n:ℝ)^2-1)/x^2) *
            (∫ w : ℝ,
              thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
                (((n:ℝ)^2-1)/x) u 0 w ∂μ)) =
        (∫ w : ℝ,
          (if n = 0 then (0:ℝ) else
            Real.exp (-((n:ℝ)^2-1)/x^2) *
              thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
                (((n:ℝ)^2-1)/x) u 0 w) ∂μ)
      simp only [if_neg hn]
      rw [integral_const_mul]
  have hbase :
      Summable (fun n : ℕ => thetaGaussianIntegratedSeriesTerm x u n 0) := by
    rw [hbaseeq]
    exact hbase_integrals
  exact hasDerivAt_tsum_of_isPreconnected hA hopen hconn
    hdiff hbound hzero hbase hv0


end W5
