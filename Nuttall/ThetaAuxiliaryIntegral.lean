import Nuttall.Existence
import Nuttall.ThetaAuxiliary
import W5.PhiTailIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Nuttall

open Filter MeasureTheory Set
open scoped Topology

theorem auxiliaryTheta_nonneg (t : ℝ) : 0 ≤ auxiliaryTheta t :=
  tsum_nonneg (fun n => by unfold auxiliarySummand; positivity)

theorem auxiliaryTheta_le_phi (t : ℝ) (ht : 0 ≤ t) :
    auxiliaryTheta t ≤ W5.Phi t := by
  rw [auxiliaryTheta, W5.Phi_eq_tsum_phiSummand]
  refine (auxiliarySummand_summable t).tsum_le_tsum ?_ (W5.phiSummand_summable t)
  intro n
  by_cases hn : n = 0
  · subst n
    simp [auxiliarySummand, W5.phiSummand_zero]
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsquare : (1 : ℝ) ≤ (n : ℝ)^2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have he : 1 ≤ Real.exp (4*t) := by
    simpa using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 4*t by positivity)
  have hprod := mul_le_mul hsquare he (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  have hx : Real.pi ≤ (n : ℝ)^2 * Real.pi * Real.exp (4*t) := by
    calc
      Real.pi ≤ Real.pi * ((n : ℝ)^2 * Real.exp (4*t)) := by
        simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left hprod Real.pi_pos.le
      _ = _ := by ring
  have hgap : 1 ≤ 2*(n : ℝ)^2 * Real.pi * Real.exp (4*t) - 3 := by
    nlinarith [Real.pi_gt_three]
  rw [W5.phiSummand_factor, auxiliarySummand]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hgap (show 0 ≤ (n : ℝ)^2 * Real.pi * Real.exp (5*t) by positivity)

theorem auxiliaryTheta_integrableOn_Ioi (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn auxiliaryTheta (Ioi t) := by
  have hd : Differentiable ℝ auxiliaryTheta :=
    fun x => (auxiliaryTheta_hasDerivAt x).differentiableAt
  have hc : Continuous auxiliaryTheta := hd.continuous
  refine (W5.Phi_integrableOn_Ioi_all t).mono' hc.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (auxiliaryTheta_nonneg x)]
  exact auxiliaryTheta_le_phi x (ht.trans (mem_Ioi.mp hx).le)

theorem auxiliaryTheta_le_exp_decay (t : ℝ) (ht : 0 ≤ t) :
    auxiliaryTheta t ≤ auxiliaryTheta 0 * Real.exp (-t) := by
  let f : ℝ → ℝ := fun x => Real.exp x * auxiliaryTheta x
  have hd (x : ℝ) : HasDerivAt f (Real.exp x * (-2 * W5.Phi x)) x := by
    convert (Real.hasDerivAt_exp x).mul (auxiliaryTheta_hasDerivAt x) using 1 <;> ring
  have hdiff : Differentiable ℝ f := fun x => (hd x).differentiableAt
  have hanti : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := mem_Ici.mp (interior_subset hx)
    rw [(hd x).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (by linarith [W5.Phi_pos x hx0])
  have h := mul_le_mul_of_nonneg_right
    (hanti (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht)
    (Real.exp_pos (-t)).le
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  change (Real.exp 0 * auxiliaryTheta 0) * Real.exp (-t) ≥
    (Real.exp t * auxiliaryTheta t) * Real.exp (-t) at h
  rw [Real.exp_zero, one_mul, show (Real.exp t * auxiliaryTheta t) * Real.exp (-t) =
    auxiliaryTheta t * (Real.exp t * Real.exp (-t)) by ring, hexp, mul_one] at h
  exact h

theorem auxiliaryTheta_tendsto_zero : Tendsto auxiliaryTheta atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℝ => auxiliaryTheta 0) atTop (𝓝 (auxiliaryTheta 0)) :=
    tendsto_const_nhds
  have hu : Tendsto (fun t => auxiliaryTheta 0 * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using hc.mul Real.tendsto_exp_neg_atTop_nhds_zero
  exact squeeze_zero' (Eventually.of_forall auxiliaryTheta_nonneg)
    ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => auxiliaryTheta_le_exp_decay t ht)) hu

/-- One integration of the auxiliary differential identity in Section 4. -/
theorem twice_psi_one_eq_auxiliary_sub_tail (t : ℝ) (ht : 0 ≤ t) :
    2 * psi 1 t = auxiliaryTheta t - tailIntegral auxiliaryTheta t := by
  have hPhi := W5.Phi_integrableOn_Ioi_all t
  have hg := auxiliaryTheta_integrableOn_Ioi t ht
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => auxiliaryTheta_hasDerivAt x) ((hPhi.const_mul (-2)).sub hg)
    auxiliaryTheta_tendsto_zero
  change 2 * (∫ x in Ici t, W5.Phi x) =
    auxiliaryTheta t - ∫ x in Ici t, auxiliaryTheta x
  rw [integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi]
  have h' : (-2 : ℝ) * (∫ x in Ioi t, W5.Phi x) -
      (∫ x in Ioi t, auxiliaryTheta x) = -auxiliaryTheta t := by
    simpa only [integral_sub (hPhi.const_mul (-2)) hg, integral_const_mul, zero_sub] using h
  linarith

#print axioms twice_psi_one_eq_auxiliary_sub_tail

end Nuttall
