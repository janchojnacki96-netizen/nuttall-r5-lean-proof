import Nuttall.PsiTwoPanelIdentity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Nuttall

open Set
open scoped BigOperators ContDiff

/-- Integral of the degree-(d-1) Taylor polynomial against the panel weight. -/
noncomputable def psiTwoPanelCorrection (d : ℕ) (a h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range d, iteratedDeriv j W5.Phi a *
    h^(j+2) / (((j:ℝ)+2) * (j.factorial:ℝ))

theorem integral_weighted_cellTaylor (d : ℕ) (a h : ℝ) :
    (∫ x in (0:ℝ)..h, x * cellTaylor W5.Phi d a 1 x) =
      psiTwoPanelCorrection (d+1) a h := by
  have hs (j : ℕ) : Continuous fun x : ℝ =>
      (iteratedDeriv j W5.Phi a / (j.factorial:ℝ)) * x^(j+1) := by fun_prop
  calc
    _ = ∫ x in (0:ℝ)..h, ∑ j ∈ Finset.range (d+1),
        (iteratedDeriv j W5.Phi a / (j.factorial:ℝ)) * x^(j+1) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [cellTaylor]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [one_pow, mul_one, pow_succ]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun j _ => (hs j).intervalIntegrable _ _)]
      unfold psiTwoPanelCorrection
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_const_mul, integral_pow, Nat.cast_add, Nat.cast_one]
      simp only [zero_pow (by omega : j+1+1 ≠ 0), sub_zero]
      rw [show (j:ℝ)+1+1 = (j:ℝ)+2 by ring]
      field_simp <;> ring

private theorem phi_cellTaylor_right_error {a x : ℝ} (ha : 0 ≤ a)
    (hx : 0 ≤ x) (h₂ : a+x ≤ 2) :
    |W5.Phi (a+x) - cellTaylor W5.Phi 35 a 1 x| ≤ (8:ℝ)^36 * 10^6 * x^36 := by
  obtain rfl | hx' := eq_or_lt_of_le hx
  · simp [cellTaylor, Finset.sum_range_succ']
  have hne : a ≠ a+1*x := by linarith only [hx']
  have hf : ContDiff ℝ (36:ℕ) W5.Phi := (contDiff_psi 0).of_le (by simp)
  obtain ⟨s, hs, hr⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf.contDiffOn
  have hs' : s ∈ Icc a (a+x) := by
    simpa only [one_mul, uIcc_of_le (le_add_of_nonneg_right hx)] using uIoo_subset_uIcc_self hs
  have hD := iteratedDeriv_phi_compact_norm_le 36 (ha.trans hs'.1) (hs'.2.trans h₂)
  rw [Real.norm_eq_abs] at hD
  rw [taylorWithinEval_eq_cellTaylor hf hne, one_mul, add_sub_cancel_left] at hr
  rw [hr, abs_div, abs_mul, abs_pow, abs_of_nonneg hx, Nat.abs_cast]
  calc
    _ ≤ (((36:ℕ).factorial:ℝ) * 8^36 * 10^6) * x^36 / ((36:ℕ).factorial:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD (by positivity)) (by positivity)
    _ = _ := by field_simp

/-- Remainder for the 36-term weighted quadrature used in the compact Ψ₂ certificate. -/
theorem psi_two_panel_error_le {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hb : a+h ≤ 2) :
    |psi 2 a - (psi 2 (a+h) + h * psi 1 (a+h) +
      psiTwoPanelCorrection 36 a h)| ≤ (8:ℝ)^36 * 10^6 * h^38 / 38 := by
  let F (x : ℝ) := x * W5.Phi (a+x)
  let P (x : ℝ) := x * cellTaylor W5.Phi 35 a 1 x
  let M (x : ℝ) := ((8:ℝ)^36 * 10^6) * x^37
  have hF : Continuous F :=
    continuous_id.mul ((psi_continuous 0).comp (continuous_const.add continuous_id))
  have hP : Continuous P := by unfold P cellTaylor; fun_prop
  have hM : Continuous M := by unfold M; fun_prop
  have hsub : (∫ x in (0:ℝ)..h, F x) = ∫ x in a..a+h, (x-a) * W5.Phi x := by
    let g (x : ℝ) := (x-a) * W5.Phi x
    have he := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := h) g a
    simpa [g, F, add_comm] using he
  rw [psi_two_eq_panel a (a+h), add_sub_cancel_left, ← hsub,
    ← integral_weighted_cellTaylor 35 a h]
  rw [show ∀ S A B : ℝ, S+A-(S+B) = A-B by intros; ring]
  change |(∫ x in (0:ℝ)..h, F x) - ∫ x in (0:ℝ)..h, P x| ≤ _
  rw [← intervalIntegral.integral_sub (hF.intervalIntegrable _ _) (hP.intervalIntegrable _ _)]
  refine (intervalIntegral.abs_integral_le_integral_abs hh).trans ?_
  have hpoint (x : ℝ) (hx : x ∈ Icc 0 h) : |F x-P x| ≤ M x := by
    dsimp [F, P, M]
    rw [← mul_sub, abs_mul, abs_of_nonneg hx.1, pow_succ]
    have h₂ : a+x ≤ 2 := by linarith only [hx.2, hb]
    nlinarith only [mul_le_mul_of_nonneg_left (phi_cellTaylor_right_error ha hx.1 h₂) hx.1]
  refine (intervalIntegral.integral_mono_on hh
    ((hF.sub hP).abs.intervalIntegrable _ _) (hM.intervalIntegrable _ _) hpoint).trans_eq ?_
  unfold M
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num <;> ring

#print axioms integral_weighted_cellTaylor
#print axioms psi_two_panel_error_le

end Nuttall
