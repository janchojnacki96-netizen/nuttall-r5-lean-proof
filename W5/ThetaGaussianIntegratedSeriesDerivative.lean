import W5.ThetaGaussianBaseTermMajorant
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiating the full transformed theta square-index series

Previous modules establish:
* first derivatives of each theta w-integral on a common open patch;
* an integrable and summable bound for their derivative integrals;
* convergence of the *undifferentiated* integrated theta terms at v=0;
* the patch is open and preconnected.

These are precisely the hypotheses of Mathlib's
`hasDerivAt_tsum_of_isPreconnected`. This module assembles them to
differentiate the n-series of transformed weighted theta integrals,
with index zero explicitly set to zero.

The result is only a first v-derivative at v=0 for fixed x and u.
No claim about the fifth Hankel determinant, higher mixed jets, or
the original Nuttall r=5 sign theorem is made here.
-/

namespace W5
open MeasureTheory

/-- The n-th transformed, integrated theta term, including
the exterior Gaussian factor. -/
noncomputable def thetaGaussianIntegratedSeriesTerm
    (x u : ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  if n = 0 then 0 else
    Real.exp (-((n:ℝ)^2-1)/x^2) *
      (∫ w : ℝ,
        thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w
        ∂(volume.restrict (Set.Ioi (0:ℝ))))

/-- Its genuine first derivative, obtained by differentiating
the individual w-integral. Index zero remains zero. -/
noncomputable def thetaGaussianIntegratedSeriesDerivative
    (x u : ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  if n = 0 then 0 else
    Real.exp (-((n:ℝ)^2-1)/x^2) *
      (∫ w : ℝ,
        thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w
        ∂(volume.restrict (Set.Ioi (0:ℝ))))

/-- The first derivative of the **whole n-series of transformed
theta w-integrals** can be interchanged with its n-sum at v=0.

The proof uses Mathlib's series differentiation theorem with a
common open connected neighborhood and an honest summable bound,
not an admitted derivative / sum interchange. -/
theorem thetaGaussianIntegratedSeries_hasDerivAt_zero
    (x u : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) :
    HasDerivAt
      (fun v : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x u n v)
      (∑' n : ℕ, thetaGaussianIntegratedSeriesDerivative x u n 0)
      (0:ℝ) := by
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
    hdiff hbound hzero hbase hzero

end W5
