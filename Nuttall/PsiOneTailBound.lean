import Nuttall.ThetaAuxiliaryIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Nuttall

open MeasureTheory Set

/-- The first square gives a common lower bound for every positive square
in the ratio between the theta kernel and the auxiliary series. -/
theorem auxiliaryTheta_mul_coordinate_le_phi (t : ℝ) :
    (2 * (Real.pi * Real.exp (4*t)) - 3) * auxiliaryTheta t ≤ W5.Phi t := by
  let X := Real.pi * Real.exp (4*t)
  have hX : 0 < X := by dsimp [X]; positivity
  change (2*X-3) * auxiliaryTheta t ≤ W5.Phi t
  rw [auxiliaryTheta, W5.Phi_eq_tsum_phiSummand, ← tsum_mul_left]
  refine ((auxiliarySummand_summable t).mul_left _).tsum_le_tsum ?_ (W5.phiSummand_summable t)
  intro n
  by_cases h : n = 0
  · subst n
    simp [auxiliarySummand, W5.phiSummand_zero]
  have hn : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith only [hn, sq_nonneg ((n:ℝ)-1)]
  have hqn : X ≤ (n:ℝ)^2*X :=
    le_trans (by simp) (mul_le_mul_of_nonneg_right hn2 hX.le)
  have hfac : W5.phiSummand n t = (2*(n:ℝ)^2*X-3)*auxiliarySummand n t := by
    rw [W5.phiSummand_factor]
    unfold auxiliarySummand X
    ring
  rw [hfac]
  exact mul_le_mul_of_nonneg_right (by linarith only [hqn])
    (by unfold auxiliarySummand; positivity)

private theorem auxiliaryTheta_exp_majorant (t s c : ℝ) (hts : t ≤ s)
    (hc : c ≤ 4 * (Real.pi * Real.exp (4*t)) - 5) :
    auxiliaryTheta s ≤ auxiliaryTheta t * Real.exp (-c*(s-t)) := by
  let F (y : ℝ) := Real.exp (c*(y-t)) * auxiliaryTheta y
  have hD (y : ℝ) : HasDerivAt F
      (Real.exp (c*(y-t)) * ((c-1)*auxiliaryTheta y - 2*W5.Phi y)) y := by
    have hl : HasDerivAt (fun z : ℝ => c*(z-t)) c y := by
      simpa using ((hasDerivAt_id y).sub_const t).const_mul c
    convert ((Real.hasDerivAt_exp (c*(y-t))).comp y hl).mul
      (auxiliaryTheta_hasDerivAt y) using 1
    · rfl
    · simp only [Function.comp_apply]
      ring
  have hDiff : Differentiable ℝ F := fun y => (hD y).differentiableAt
  have hAnti : AntitoneOn F (Ici t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hDiff.continuous.continuousOn hDiff.differentiableOn
    intro y hy
    have hy' : t ≤ y := mem_Ici.mp (interior_subset hy)
    have hyc : c ≤ 4*(Real.pi*Real.exp (4*y))-5 := hc.trans (by
      have he : Real.exp (4*t) ≤ Real.exp (4*y) := Real.exp_le_exp.mpr (by linarith)
      linarith only [mul_le_mul_of_nonneg_left he Real.pi_pos.le])
    rw [(hD y).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hprod := mul_le_mul_of_nonneg_right
      (show c-1 ≤ 2*(2*(Real.pi*Real.exp (4*y))-3) by linarith only [hyc])
      (auxiliaryTheta_nonneg y)
    nlinarith only [hprod, auxiliaryTheta_mul_coordinate_le_phi y]
  have h := mul_le_mul_of_nonneg_right
    (hAnti (by simp) (mem_Ici.2 hts) hts) (Real.exp_pos (-c*(s-t))).le
  have he : Real.exp (c*(s-t)) * Real.exp (-c*(s-t)) = 1 := by
    rw [← Real.exp_add, show c*(s-t) + -c*(s-t) = 0 by ring, Real.exp_zero]
  have hs : F s * Real.exp (-c*(s-t)) = auxiliaryTheta s := by
    unfold F
    rw [mul_right_comm, he, one_mul]
  rwa [hs, show F t = auxiliaryTheta t by simp [F]] at h

/-- Bounding the correction integral by an exponential tail leaves a lower bound
for the first integrated theta kernel from the auxiliary series at one point. -/
theorem psi_one_ge_auxiliary_mul_rate (t c : ℝ) (ht : 0 ≤ t) (hc₀ : 0 < c)
    (hc : c ≤ 4 * (Real.pi * Real.exp (4*t)) - 5) :
    (auxiliaryTheta t - auxiliaryTheta t/c)/2 ≤ psi 1 t := by
  have hsplit (s : ℝ) : auxiliaryTheta t * Real.exp (-c*(s-t)) =
      (auxiliaryTheta t * Real.exp (c*t)) * Real.exp (-c*s) := by
    rw [show -c*(s-t) = c*t + -c*s by ring, Real.exp_add, mul_assoc]
  have hcmp := setIntegral_mono_on (auxiliaryTheta_integrableOn_Ioi t ht)
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc₀) t).const_mul
      (auxiliaryTheta t * Real.exp (c*t))) measurableSet_Ioi
    (fun s hs => by
      rw [← hsplit]
      exact auxiliaryTheta_exp_majorant t s c (mem_Ioi.mp hs).le hc)
  simp only [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hc₀)] at hcmp
  have he : Real.exp (c*t) * Real.exp (-c*t) = 1 := by
    rw [← Real.exp_add, show c*t + -c*t = 0 by ring, Real.exp_zero]
  have hh : (auxiliaryTheta t * Real.exp (c*t)) * (-Real.exp (-c*t) / -c) =
      auxiliaryTheta t/c := by
    rw [neg_div_neg_eq, ← mul_div_assoc, mul_assoc, he, mul_one]
  rw [hh] at hcmp
  have h := twice_psi_one_eq_auxiliary_sub_tail t ht
  rw [tailIntegral, integral_Ici_eq_integral_Ioi] at h
  linarith only [h, hcmp]

#print axioms psi_one_ge_auxiliary_mul_rate

end Nuttall
