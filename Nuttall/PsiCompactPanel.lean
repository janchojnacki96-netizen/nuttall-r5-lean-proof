import Nuttall.CompactTaylor
import Nuttall.PsiHankelJets

namespace Nuttall

open Set
open scoped BigOperators ContDiff

/-- Taylor terms used to transfer an enclosure from the right endpoint to the left. -/
noncomputable def psiPanelCorrection (m d : ℕ) (a h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range d, iteratedDeriv j (psi m) a * h^(j+1) / ((j+1).factorial : ℝ)

/-- The tail integral at the left endpoint is the right endpoint plus the
integrated Taylor polynomial, with a deterministic remainder. -/
theorem psiPanel_error_le {m d : ℕ} {a h C : ℝ} (hh : 0 ≤ h)
    (hDeriv : ∀ x ∈ Icc a (a+h), |iteratedDeriv d (psi m) x| ≤ C) :
    |psi (m+1) a - (psi (m+1) (a+h) + psiPanelCorrection m d a h)| ≤
      C * h^(d+1) / ((d+1).factorial : ℝ) := by
  have hf : ContDiff ℝ (d+1 : ℕ) (psi (m+1)) :=
    (contDiff_psi (m+1)).of_le (by simp)
  have hPoly : cellTaylor (psi (m+1)) d a h 1 =
      psi (m+1) a - psiPanelCorrection m d a h := by
    rw [cellTaylor, psiPanelCorrection, Finset.sum_range_succ']
    simp only [one_pow, mul_one, iteratedDeriv_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, iteratedDeriv_succ_psi_succ]
    simp_rw [neg_mul, neg_div, Finset.sum_neg_distrib]
    ring
  obtain rfl | hh' := eq_or_lt_of_le hh
  · simp only [add_zero, psiPanelCorrection, zero_pow (Nat.succ_ne_zero _), mul_zero,
      zero_div, Finset.sum_const_zero, sub_self, abs_zero, le_refl]
  have he : a ≠ a+h := by linarith only [hh']
  obtain ⟨x, hx, hr⟩ := taylor_mean_remainder_lagrange_iteratedDeriv he hf.contDiffOn
  have heval : taylorWithinEval (psi (m+1)) d (uIcc a (a+h)) a (a+h) =
      cellTaylor (psi (m+1)) d a h 1 := by
    have he' : a ≠ a+h*1 := by simpa only [mul_one] using he
    simpa only [mul_one] using taylorWithinEval_eq_cellTaylor hf he'
  have hx' : x ∈ Icc a (a+h) := by
    have hax : a ≤ a+h := by linarith only [hh']
    simpa only [uIcc_of_le hax] using uIoo_subset_uIcc_self hx
  rw [heval, hPoly, add_sub_cancel_left, iteratedDeriv_succ_psi_succ] at hr
  rw [show psi (m+1) a - (psi (m+1) (a+h) + psiPanelCorrection m d a h) =
      -(psi (m+1) (a+h) - (psi (m+1) a - psiPanelCorrection m d a h)) by ring, hr]
  simp only [abs_neg, abs_div, abs_mul, Nat.abs_cast, abs_of_nonneg (pow_nonneg hh'.le (d+1))]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDeriv x hx') (pow_nonneg hh'.le _)) (by positivity)

#print axioms psiPanel_error_le

end Nuttall
