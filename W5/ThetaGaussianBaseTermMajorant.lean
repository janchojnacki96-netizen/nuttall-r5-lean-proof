import W5.ThetaGaussianSummableOpenPatch

/-!
# Gaussian domination of the original, undifferentiated theta terms

Mathlib's differentiation-of-series theorem needs the undifferentiated
series to converge at one basepoint in addition to the summably
dominated derivatives. This module derives a pointwise Gaussian bound
on the genuine *undifferentiated* weighted theta integrand, retaining
the exterior theta factor exp(-(p-1)/x²).

The parameter assumptions are precisely those of the small box used
for the first-derivative estimates. No series differentiation
claim or Nuttall r=5 determinant sign is made here.
-/

namespace W5
open MeasureTheory

/-- The genuine weighted Gaussian integrand, including the original
outer square-index factor, is bounded by a polynomial-Gaussian
product uniformly on the shrinking parameter box. -/
theorem thetaGaussian_small_box_base_integrand_product_bound
    (x p u v w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hw : 0 ≤ w) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Real.exp (-(p-1)/x^2) *
      thetaWeightedGaussianIntegrand x p ((p-1)/x) u v w ≤
      Real.exp (3/4) *
        ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
          ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w))) := by
  have hpPos : 0 < p := by linarith
  obtain ⟨_, hxu⟩ :=
    thetaGaussian_small_box_inside_local_patch x u hx hx1 hu
  obtain ⟨_, hxv⟩ :=
    thetaGaussian_small_box_inside_local_patch x v hx hx1 hv
  have hweighted := thetaGaussian_weighted_uniform_bound
    x p ((p-1)/x) u v w hpPos hw hxu hxv
  have hdecay :=
    thetaGaussian_small_box_weighted_decay x p u v hx hx1 hp hu hv
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hfrac : x^2/p ≤ 1 :=
    (div_le_iff₀ hpPos).2 (by linarith)
  have hdivw : w*x^2/p ≤ w := by
    calc
      w*x^2/p = w*(x^2/p) := by ring
      _ ≤ w*1 := mul_le_mul_of_nonneg_left hfrac hw
      _ = w := by ring
  have hpoly : 0 ≤ w^2+w+1 := by positivity
  have hweight :
      1+w*x^2/p ≤ (p+1)*(w^2+w+1) := by
    have h1 : 1+w*x^2/p ≤ (w^2+w+1) := by
      nlinarith [hdivw, sq_nonneg w]
    have h2 : (w^2+w+1) ≤ (p+1)*(w^2+w+1) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ p) hpoly]
    exact h1.trans h2
  have hweight_nonneg : 0 ≤ 1+w*x^2/p := by
    have hterm : 0 ≤ w*x^2/p :=
      div_nonneg (mul_nonneg hw (sq_nonneg x)) hpPos.le
    linarith
  have hE : 0 ≤ Real.exp (3/4) *
      Real.exp (-((47:ℝ)/64)*p) *
      Real.exp (-((1:ℝ)/4)*w) := by positivity
  calc
    Real.exp (-(p-1)/x^2) *
        thetaWeightedGaussianIntegrand x p ((p-1)/x) u v w ≤
      Real.exp (-(p-1)/x^2) *
        (Real.exp (-((p-1)/x)*(u+v)-p*u*v) *
          (1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := by
            unfold thetaWeightedGaussianIntegrand
            exact mul_le_mul_of_nonneg_left hweighted
              (Real.exp_nonneg _)
    _ = (Real.exp (-(p-1)/x^2) *
          Real.exp (-((p-1)/x)*(u+v)-p*u*v)) *
        ((1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) := by ring
    _ ≤ (Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p)) *
        ((1+w*x^2/p)*Real.exp (-((1:ℝ)/4)*w)) :=
          mul_le_mul_of_nonneg_right hdecay
            (mul_nonneg hweight_nonneg (Real.exp_nonneg _))
    _ = (1+w*x^2/p) *
        (Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p) *
          Real.exp (-((1:ℝ)/4)*w)) := by ring
    _ ≤ ((p+1)*(w^2+w+1)) *
        (Real.exp (3/4)*Real.exp (-((47:ℝ)/64)*p) *
          Real.exp (-((1:ℝ)/4)*w)) :=
          mul_le_mul_of_nonneg_right hweight hE
    _ = Real.exp (3/4) *
        ((p+1)*Real.exp (-((47:ℝ)/64)*p) *
          ((w^2+w+1)*Real.exp (-((1:ℝ)/4)*w))) := by ring

/-- In the actual theta series p=n², n>=1, the weighted
undifferentiated term is bounded by the product majorant
already known to be summable in n and integrable in w. -/
theorem thetaGaussian_nonzero_index_base_integrand_le_product
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (u v w : ℝ) (hw : 0 ≤ w)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Real.exp (-((n:ℝ)^2-1)/x^2) *
      thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) u v w ≤
      Real.exp (3/4) * thetaGaussianProductMajorant n w := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith [sq_nonneg (n:ℝ)]
  have h := thetaGaussian_small_box_base_integrand_product_bound
    x ((n:ℝ)^2) u v w hx hx1 hp hw hu hv
  simpa only [thetaGaussianProductMajorant] using h


/-- The genuine undifferentiated n-th weighted theta integrand,
including its exterior Gaussian; index zero is identically zero
to match the original theta series. -/
noncomputable def thetaGaussianBaseSeriesTerm
    (x u v : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  if n = 0 then 0 else
    Real.exp (-((n:ℝ)^2-1)/x^2) *
      thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) u v w

/-- Measurability for the original weighted theta terms is
unconditional, including the special zero index. -/
theorem thetaGaussianBaseSeriesTerm_measurable
    (x u v : ℝ) (n : ℕ) :
    Measurable (thetaGaussianBaseSeriesTerm x u v n) := by
  by_cases hn : n = 0
  · subst n
    change Measurable (fun _ : ℝ => (0:ℝ))
    exact measurable_const
  · have hm : Measurable (fun w : ℝ =>
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w) :=
      measurable_const.mul
        (thetaWeightedGaussian_measurable
          x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v)
    change Measurable (fun w : ℝ =>
      if n = 0 then (0:ℝ) else
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w)
    simpa only [if_neg hn] using hm

/-- Unconditional countable-sum / w-integral exchange for the
undifferentiated theta terms in the small box. In particular the
series of basepoint integrated terms is summable, which is needed
to apply Mathlib's derivative-of-tsum theorem. -/
theorem thetaGaussianBaseSeries_integral_hasSum
    (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    HasSum
      (fun n : ℕ =>
        ∫ w : ℝ, thetaGaussianBaseSeriesTerm x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, ∑' n : ℕ,
        thetaGaussianBaseSeriesTerm x u v n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let C : ℝ := Real.exp (3/4)
  let a : ℕ → ℝ := fun n =>
    C * (((n:ℝ)^2+1)*Real.exp (-((47:ℝ)/64)*(n:ℝ)^2))
  let b : ℝ → ℝ := fun w =>
    (w^2+w+1)*Real.exp (-((1:ℝ)/4)*w)
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hA : Summable a := by
    change Summable (fun n : ℕ =>
      C * (((n:ℝ)^2+1)*Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)))
    exact thetaGaussianProductMajorant_index_factor_summable.mul_left C
  have hB : Integrable b μ := by
    change IntegrableOn b (Set.Ioi (0:ℝ)) volume
    simpa only [b, one_mul] using
      (thetaGaussian_quadratic_exp_integrable (1:ℝ) 1 1)
  have hF : ∀ n : ℕ,
      AEStronglyMeasurable (thetaGaussianBaseSeriesTerm x u v n) μ := by
    intro n
    exact (thetaGaussianBaseSeriesTerm_measurable x u v n).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ∀ n : ℕ, ‖thetaGaussianBaseSeriesTerm x u v n w‖ ≤ a n*b w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw n
    have hw0 : 0 ≤ w := hw.le
    by_cases hn : n = 0
    · have ha : 0 ≤ a n := by
        dsimp [a, C]
        positivity
      have hb : 0 ≤ b w := by
        dsimp [b]
        positivity
      simpa only [thetaGaussianBaseSeriesTerm, if_pos hn,
        norm_zero] using (mul_nonneg ha hb)
    · have hn1 : 1 ≤ n := by omega
      have hvn : 0 < (n:ℝ)^2 := by
        have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        nlinarith
      have hbase : 0 ≤ 1+w*x^2/(n:ℝ)^2 := by
        have hterm : 0 ≤ w*x^2/(n:ℝ)^2 :=
          div_nonneg (mul_nonneg hw0 (sq_nonneg x)) hvn.le
        linarith
      have hnonneg : 0 ≤
          Real.exp (-((n:ℝ)^2-1)/x^2) *
            thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u v w := by
        have hweighted : 0 ≤
            thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) u v w := by
          unfold thetaWeightedGaussianIntegrand thetaGaussianModel
          exact mul_nonneg
            (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hbase _))
            (Real.exp_nonneg _)
        exact mul_nonneg (Real.exp_nonneg _) hweighted
      have heq : a n*b w =
          C * thetaGaussianProductMajorant n w := by
        dsimp [a, b, thetaGaussianProductMajorant]
        ring
      rw [heq]
      have h := thetaGaussian_nonzero_index_base_integrand_le_product
        x hx hx1 n hn1 u v w hw0 hu hv
      change ‖if n = 0 then (0:ℝ) else
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaWeightedGaussianIntegrand x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) u v w‖ ≤
              C * thetaGaussianProductMajorant n w
      rw [if_neg hn, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact h
  exact hasSum_integral_of_separable_bound μ
    (thetaGaussianBaseSeriesTerm x u v) a b
    hA hB hF hbound

/-- The undifferentiated integrated theta series converges for
all parameters in the small coordinate box, in particular at v=0. -/
theorem thetaGaussianBaseSeries_integrals_summable
    (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaGaussianBaseSeriesTerm x u v n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
  (thetaGaussianBaseSeries_integral_hasSum x u v hx hx1 hu hv).summable

end W5
