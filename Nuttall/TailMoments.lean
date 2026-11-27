import Nuttall.TailIteration
import W5.ThetaTermIntegrability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace Nuttall

open MeasureTheory Set

private theorem integrate_sub_pow (j : ℕ) {t s : ℝ} (hts : t ≤ s) :
    (∫ u in Icc t s, (s-u)^j) = (s-t)^(j+1) / (j+1 : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hts]
  rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x^j) s, sub_self]
  simp [integral_pow]

private theorem polynomial_exp_integrable (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => s^j * Real.exp (-(1/2 : ℝ)*s)) (Ici t) := by
  have h := W5.theta_rpow_exp_integrableOn (1/2) (j : ℝ)
    (by norm_num) (by positivity)
  exact ((integrableOn_Ici_iff_integrableOn_Ioi).2
    (by simpa only [Real.rpow_natCast] using h)).mono_set (Ici_subset_Ici.mpr ht)

/-- Change the order of integration over the triangle t ≤ u ≤ s. -/
private theorem integrate_auxiliary_triangle (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in Ici t, ∫ s in Ici u, (s-u)^j * auxiliaryTheta s) =
      (∫ s in Ici t, (s-t)^(j+1) * auxiliaryTheta s) / (j+1 : ℝ) := by
  let μ := volume.restrict (Ici t)
  let F (u s : ℝ) := (Ici u).indicator (fun y => (y-u)^j * auxiliaryTheta y) s
  have hg := tailIterate_auxiliary_continuous 0
  change Continuous auxiliaryTheta at hg
  have hF : Measurable (Function.uncurry F) := by
    have heq : Function.uncurry F =
        {z : ℝ × ℝ | z.1 ≤ z.2}.indicator
          (fun z : ℝ × ℝ => (z.2-z.1)^j * auxiliaryTheta z.2) := by
      funext z
      by_cases h : z.1 ≤ z.2 <;>
        simp [Function.uncurry, F, indicator_apply, h]
    rw [heq]
    exact (((continuous_snd.sub continuous_fst).pow j).mul
      (hg.comp continuous_snd)).measurable.indicator measurableSet_le'
  have h0 : Integrable (fun u : ℝ => Real.exp (-(1/2 : ℝ)*u)) μ := by
    simpa using (polynomial_exp_integrable 0 ht)
  have hbig : Integrable
      (fun z : ℝ × ℝ => Real.exp (-(1/2 : ℝ)*z.1) *
        (auxiliaryTheta 0 * (z.2^j * Real.exp (-(1/2 : ℝ)*z.2)))) (μ.prod μ) :=
    h0.mul_prod ((polynomial_exp_integrable j ht).const_mul (auxiliaryTheta 0))
  have hmem : ∀ᵐ z ∂μ.prod μ, z ∈ Ici t ×ˢ Ici t := by
    apply (ae_prod_mem_iff_ae_ae_mem (measurableSet_Ici.prod measurableSet_Ici)).2
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact ⟨hu, hs⟩
  have hInt : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine hbig.mono' hF.aestronglyMeasurable ?_
    filter_upwards [hmem] with z hz
    have hu : 0 ≤ z.1 := ht.trans hz.1
    have hs : 0 ≤ z.2 := ht.trans hz.2
    change ‖F z.1 z.2‖ ≤ _
    by_cases h : z.1 ≤ z.2
    · have hp : (z.2-z.1)^j ≤ z.2^j :=
        pow_le_pow_left₀ (sub_nonneg.mpr h) (sub_le_self _ hu) _
      have he : Real.exp (-z.2) ≤
          Real.exp (-(1/2 : ℝ)*z.1) * Real.exp (-(1/2 : ℝ)*z.2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have hbound := auxiliaryTheta_le_exp_decay z.2 hs
      rw [F, indicator_of_mem (show z.2 ∈ Ici z.1 from h),
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.mpr h) _)
          (auxiliaryTheta_nonneg _))]
      calc
        (z.2-z.1)^j * auxiliaryTheta z.2 ≤ z.2^j * auxiliaryTheta z.2 :=
          mul_le_mul_of_nonneg_right hp (auxiliaryTheta_nonneg _)
        _ ≤ z.2^j * (auxiliaryTheta 0 * Real.exp (-z.2)) :=
          mul_le_mul_of_nonneg_left hbound (pow_nonneg hs _)
        _ ≤ z.2^j * (auxiliaryTheta 0 *
            (Real.exp (-(1/2 : ℝ)*z.1) * Real.exp (-(1/2 : ℝ)*z.2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (auxiliaryTheta_nonneg _))
            (pow_nonneg hs _)
        _ = _ := by ring
    · rw [F, indicator_of_notMem (show z.2 ∉ Ici z.1 from h), norm_zero]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (auxiliaryTheta_nonneg _) (mul_nonneg (pow_nonneg hs _) (Real.exp_pos _).le))
  have hleft : (∫ u, ∫ s, F u s ∂μ ∂μ) =
      ∫ u in Ici t, ∫ s in Ici u, (s-u)^j * auxiliaryTheta s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hsub : Ici u ⊆ Ici t := Ici_subset_Ici.mpr hu
    rw [F, integral_indicator measurableSet_Ici]
    change (∫ s, (s-u)^j * auxiliaryTheta s ∂(volume.restrict (Ici t)).restrict (Ici u)) = _
    rw [Measure.restrict_restrict_of_subset hsub]
  have hright : (∫ s, ∫ u, F u s ∂μ ∂μ) =
      ∫ s in Ici t, ((s-t)^(j+1) * auxiliaryTheta s) / (j+1 : ℝ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have hEq : (fun u => F u s) =
        (Iic s).indicator (fun u => (s-u)^j * auxiliaryTheta s) := by
      funext u
      by_cases hu : u ≤ s <;> simp [F, indicator_apply, hu]
    rw [hEq, integral_indicator measurableSet_Iic]
    change (∫ u, (s-u)^j * auxiliaryTheta s ∂(volume.restrict (Ici t)).restrict (Iic s)) = _
    rw [Measure.restrict_restrict measurableSet_Iic, inter_comm, Ici_inter_Iic, integral_mul_const,
      integrate_sub_pow j hs]
    ring
  calc
    _ = ∫ u, ∫ s, F u s ∂μ ∂μ := hleft.symm
    _ = ∫ s, ∫ u, F u s ∂μ ∂μ := integral_integral_swap hInt
    _ = _ := hright.trans (integral_div _ _)

/-- The auxiliary tail iterates are normalized moments of the same kernel. -/
theorem tailIterate_auxiliary_eq_moment (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    tailIterate auxiliaryTheta (j+1) t =
      (∫ s in Ici t, (s-t)^j * auxiliaryTheta s) / (j.factorial : ℝ) := by
  induction j generalizing t with
  | zero => simp [tailIterate, tailIntegral]
  | succ j ih =>
    change (∫ u in Ici t, tailIterate auxiliaryTheta (j+1) u) = _
    have hEq : (∫ u in Ici t, tailIterate auxiliaryTheta (j+1) u) =
        ∫ u in Ici t, (∫ s in Ici u, (s-u)^j * auxiliaryTheta s) / (j.factorial : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      exact ih u (ht.trans hu)
    rw [hEq, integral_div, integrate_auxiliary_triangle j ht, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ, div_div_eq_div_mul]

#print axioms tailIterate_auxiliary_eq_moment

end Nuttall
