import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Nuttall

open MeasureTheory Set intervalIntegral
open scoped Real

/-- The normalized angular average of the Gaussian in the cosine variable
is bounded by an explicit ordinary Gaussian integral. -/
theorem shiftAngularGaussian_average {b : ℝ} (hb : 0 < b) :
    (1/(2*π)) * (∫ θ in (0:ℝ)..2*π, Real.exp (-b*(Real.cos θ)^2)) ≤
      Real.sqrt π / (2*Real.sqrt b) := by
  let F (t : ℝ) := Real.exp (-b*(Real.cos t)^2)
  let G (t : ℝ) := Real.exp (-b*(Real.sin t)^2)
  let a : ℝ := b*(2/π)^2
  let H (t : ℝ) := Real.exp (-a*t^2)
  have hcF : Continuous F := by unfold F; fun_prop
  have hcG : Continuous G := by unfold G; fun_prop
  have hcH : Continuous H := by unfold H; fun_prop
  have ha : 0 < a := by unfold a; positivity
  have hp : 0 < π := Real.pi_pos
  have hz : (0 : ℝ) ≤ π/2 := by positivity
  have hwhole : (∫ t in (0:ℝ)..2*π, F t) = 2*(∫ t in (0:ℝ)..π, F t) := by
    have h₂ : (∫ t in π..2*π, F t) = ∫ t in (0:ℝ)..π, F t := by
      have h := integral_comp_add_right (a := 0) (b := π) F π
      simp only [zero_add, ← two_mul] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro t _
      simp [F, Real.cos_add_pi]
    rw [← integral_add_adjacent_intervals (hcF.intervalIntegrable _ _) (hcF.intervalIntegrable _ _), h₂]
    ring
  have hhalf : (∫ t in (0:ℝ)..π, F t) = 2*(∫ t in (0:ℝ)..π/2, F t) := by
    have h₂ : (∫ t in π/2..π, F t) = ∫ t in (0:ℝ)..π/2, F t := by
      have h := integral_comp_sub_left (a := 0) (b := π/2) F π
      rw [show π-π/2 = π/2 by ring, sub_zero] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro t _
      simp [F, Real.cos_pi_sub]
    rw [← integral_add_adjacent_intervals (hcF.intervalIntegrable _ _) (hcF.intervalIntegrable _ _), h₂]
    ring
  have hquarter : (∫ t in (0:ℝ)..π/2, F t) = ∫ t in (0:ℝ)..π/2, G t := by
    have h := integral_comp_sub_left (a := 0) (b := π/2) F (π/2)
    rw [sub_self, sub_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [F, G, Real.cos_pi_div_two_sub]
  have hGH : (∫ t in (0:ℝ)..π/2, G t) ≤ ∫ t in (0:ℝ)..π/2, H t := by
    apply intervalIntegral.integral_mono_on hz (hcG.intervalIntegrable _ _) (hcH.intervalIntegrable _ _)
    intro t ht
    have hsin := Real.mul_le_sin ht.1 ht.2
    have ht' : 0 ≤ 2/π*t := mul_nonneg (by positivity) ht.1
    have hsq := pow_le_pow_left₀ ht' hsin 2
    apply Real.exp_le_exp.mpr
    dsimp [a]
    rw [mul_pow] at hsq
    calc
      _ ≤ -b * ((2/π)^2*t^2) := mul_le_mul_of_nonpos_left hsq (neg_nonpos.2 hb.le)
      _ = _ := by ring
  have hH : (∫ t in (0:ℝ)..π/2, H t) ≤ Real.sqrt (π/a) / 2 := by
    rw [intervalIntegral.integral_of_le hz, ← integral_gaussian_Ioi]
    exact setIntegral_mono_set ((integrable_exp_neg_mul_sq ha).integrableOn)
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
      (Ioc_subset_Ioi_self.eventuallySubset)
  change (1/(2*π)) * (∫ θ in (0:ℝ)..2*π, F θ) ≤ _
  rw [hwhole, hhalf, hquarter]
  have hbound := hGH.trans hH
  have hscale : 0 ≤ 1/(2*π) := by positivity
  calc
    _ ≤ (1/(2*π)) * (2*(2*(Real.sqrt (π/a)/2))) := by gcongr
    _ = _ := by
      dsimp [a]
      rw [Real.sqrt_div hp.le, Real.sqrt_mul hb.le, Real.sqrt_sq (by positivity)]
      field_simp [hp.ne', (Real.sqrt_pos.2 hb).ne']

#print axioms shiftAngularGaussian_average

end Nuttall
