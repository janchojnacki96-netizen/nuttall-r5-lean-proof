import Nuttall.AuxiliarySeries
import Nuttall.MomentWeightCalculus
import Nuttall.WeightedMomentDeterminant

namespace Nuttall

open Filter MeasureTheory Set
open scoped Topology

theorem auxiliarySignedJet_zero (t : ℝ) : auxiliarySignedJet 0 t = auxiliaryTheta t := by
  simp [auxiliarySignedJet, auxiliaryTheta, auxiliaryWeightedSummand, auxiliaryDerivativePolynomial]

private theorem auxiliarySignedJet_continuous (j : ℕ) : Continuous (auxiliarySignedJet j) :=
  (show Differentiable ℝ (auxiliarySignedJet j) from
    fun t => (auxiliarySignedJet_hasDerivAt j t).differentiableAt).continuous

private theorem power_mul_signedJet_norm_le {C t s : ℝ} (k j : ℕ)
    (hc : 0 ≤ C) (ht : 0 ≤ t) (hs : t ≤ s)
    (hdecay : ‖auxiliarySignedJet j s‖ ≤ C * Real.exp (-s)) :
    ‖(s-t)^k * auxiliarySignedJet j s‖ ≤ C * (s^k * Real.exp (-s)) := by
  have hs0 := ht.trans hs
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hs) _)]
  calc
    _ ≤ (s-t)^k * (C * Real.exp (-s)) :=
      mul_le_mul_of_nonneg_left hdecay (pow_nonneg (sub_nonneg.mpr hs) _)
    _ ≤ s^k * (C * Real.exp (-s)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sub_nonneg.mpr hs) (sub_le_self _ ht) _)
        (mul_nonneg hc (Real.exp_nonneg _))
    _ = _ := by ring

theorem power_mul_signedJet_integrable (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s => (s-t)^k * auxiliarySignedJet j s) (Ici t) := by
  obtain ⟨C, hC, hdecay⟩ := auxiliaryWeightedSeries_decay (auxiliaryDerivativePolynomial j)
  have hcont : Continuous (fun s => (s-t)^k * auxiliarySignedJet j s) :=
    ((continuous_id.sub continuous_const).pow k).mul (auxiliarySignedJet_continuous j)
  refine ((polynomial_exp_integrable k ht).const_mul C).mono' hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  have hs0 : 0 ≤ s := ht.trans hs
  have h := power_mul_signedJet_norm_le k j hC ht hs (hdecay s hs0)
  exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) (pow_nonneg hs0 k)) hC)

theorem power_mul_signedJet_tendsto_zero (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun s => (s-t)^k * auxiliarySignedJet j s) atTop (𝓝 0) := by
  obtain ⟨C, hC, hdecay⟩ := auxiliaryWeightedSeries_decay (auxiliaryDerivativePolynomial j)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hC' : Tendsto (fun _ : ℝ => C) atTop (𝓝 C) := tendsto_const_nhds
  have hb : Tendsto (fun s : ℝ => C * (s^k * Real.exp (-s))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hC'.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k)
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hb
  filter_upwards [eventually_ge_atTop t] with s hs
  exact power_mul_signedJet_norm_le k j hC ht hs (hdecay s (ht.trans hs))

private theorem weight_mul_signedJet_eq (k j : ℕ) (t : ℝ) :
    (fun s => tailMomentWeight k (s-t) * auxiliarySignedJet j s) =
      (fun s => (s-t)^k * auxiliarySignedJet j s / (k.factorial : ℝ)) -
      (fun s => (s-t)^(k+1) * auxiliarySignedJet j s / ((k+1).factorial : ℝ)) := by
  funext s
  simp only [tailMomentWeight, Pi.sub_apply, sub_mul, div_mul_eq_mul_div]

theorem weight_mul_signedJet_integrable (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s => tailMomentWeight k (s-t) * auxiliarySignedJet j s) (Ici t) := by
  rw [weight_mul_signedJet_eq]
  exact ((power_mul_signedJet_integrable k j ht).div_const (k.factorial : ℝ)).sub
    ((power_mul_signedJet_integrable (k+1) j ht).div_const ((k+1).factorial : ℝ))

theorem weight_mul_signedJet_tendsto_zero (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun s => tailMomentWeight k (s-t) * auxiliarySignedJet j s) atTop (𝓝 0) := by
  rw [weight_mul_signedJet_eq]
  have h1 := (power_mul_signedJet_tendsto_zero k j ht).div_const (k.factorial : ℝ)
  have h2 := (power_mul_signedJet_tendsto_zero (k+1) j ht).div_const ((k+1).factorial : ℝ)
  simpa only [zero_div, sub_zero, Pi.sub_apply] using h1.sub h2

/-- A single integration by parts, with both endpoint terms zero. -/
theorem integral_weight_signedJet_succ (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Ici t, tailMomentWeight (k+1) (s-t) * auxiliarySignedJet (j+1) s) =
      ∫ s in Ici t, tailMomentWeight k (s-t) * auxiliarySignedJet j s := by
  let u := fun s => tailMomentWeight (k+1) (s-t)
  let u' := fun s => tailMomentWeight k (s-t)
  let v := auxiliarySignedJet j
  let v' := fun s => -auxiliarySignedJet (j+1) s
  have hu (s : ℝ) : HasDerivAt u (u' s) s := by
    simpa only [u, u', Function.comp_def, id_eq, mul_one] using
      (tailMomentWeight_succ_hasDerivAt k (s-t)).comp s ((hasDerivAt_id s).sub_const t)
  have hboundary : Tendsto (u * v) (𝓝[>] t) (𝓝 0) := by
    have hc : Continuous u :=
      (show Differentiable ℝ u from fun s => (hu s).differentiableAt).continuous
    have h := (hc.mul (auxiliarySignedJet_continuous j)).continuousAt (x := t)
    have hz : u t * v t = 0 := by simp [u, tailMomentWeight_succ_zero]
    rw [hz] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hi : IntegrableOn (u * v') (Ioi t) := by
    simpa only [u, v', Pi.mul_apply, mul_neg] using
      ((weight_mul_signedJet_integrable (k+1) (j+1) ht).mono_set Ioi_subset_Ici_self).neg
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun s _ => hu s) (fun s _ => auxiliarySignedJet_hasDerivAt j s) hi
    ((weight_mul_signedJet_integrable k j ht).mono_set Ioi_subset_Ici_self)
    hboundary (weight_mul_signedJet_tendsto_zero (k+1) j ht)
  simp only [u, u', v, v', mul_neg, integral_neg, sub_zero, zero_sub, neg_inj] at hparts
  simpa only [integral_Ici_eq_integral_Ioi] using hparts

/-- Transfer a column's derivatives from the weight to the theta series. -/
theorem integral_weight_signedJet (k j : ℕ) (hjk : j ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Ici t, tailMomentWeight k (s-t) * auxiliarySignedJet j s) =
      ∫ s in Ici t, tailMomentWeight (k-j) (s-t) * auxiliaryTheta s := by
  induction j generalizing k with
  | zero => simp only [auxiliarySignedJet_zero, Nat.sub_zero]
  | succ j ih =>
    obtain ⟨l, rfl⟩ : ∃ l, k = l+1 := ⟨k-1, by omega⟩
    rw [integral_weight_signedJet_succ l j ht, ih l (by omega)]
    rw [show l+1-(j+1) = l-j by omega]

/-- The moment determinant with separate rows and columns, ready for Andréief. -/
theorem twice_pow_signed_wronskian_eq_separated_moments {p m : ℕ} (hm : 2*p ≤ m)
    (t : ℝ) (ht : 0 ≤ t) :
    (2 : ℝ)^p * ((-1 : ℝ)^(p*(p-1)/2) * wronskian (psi m) p t) =
      (Matrix.of (fun (i j : Fin p) =>
        ∫ s in Ici t, tailMomentWeight (m-(p-1)+i.val-2) (s-t) * auxiliarySignedJet j.val s)).det := by
  rw [twice_pow_signed_wronskian_eq_moment_det hm t ht]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hj := j.isLt
  have hle : j.val ≤ m-(p-1)+i.val-2 := by omega
  simpa only [Matrix.of_apply, show m-(p-1)+i.val-2-j.val =
    m-(p-1)+i.val-j.val-2 by omega] using
    (integral_weight_signedJet _ _ hle ht).symm

#print axioms weight_mul_signedJet_integrable
#print axioms weight_mul_signedJet_tendsto_zero
#print axioms integral_weight_signedJet_succ
#print axioms integral_weight_signedJet
#print axioms twice_pow_signed_wronskian_eq_separated_moments

end Nuttall
