import Nuttall.PhiCompactJetBounds
import Nuttall.PsiCompactPanel

namespace Nuttall

open Set
open scoped BigOperators ContDiff

theorem iteratedDeriv_iteratedDeriv_eq (f : ℝ → ℝ) (k l : ℕ) :
    iteratedDeriv k (iteratedDeriv l f) = iteratedDeriv (k+l) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

private theorem contDiff_psi_jet (m l : ℕ) : ContDiff ℝ ∞ (iteratedDeriv l (psi m)) := by
  obtain ⟨hc, hd⟩ := contDiff_iff_iteratedDeriv.mp (contDiff_psi m)
  apply contDiff_iff_iteratedDeriv.mpr
  constructor
  · intro k _
    rw [iteratedDeriv_iteratedDeriv_eq]
    exact hc _ (by simp)
  · intro k _
    rw [iteratedDeriv_iteratedDeriv_eq]
    exact hd _ (by simp)

/-- Quantitative error for one backwards quadrature panel for the zeroth Hankel entry. -/
theorem psiOne_panel_error_le {d : ℕ} {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hb : a+h ≤ 2) :
    |psi 1 a - (psi 1 (a+h) + psiPanelCorrection 0 d a h)| ≤
      (((d.factorial : ℝ) * 8^d) * 10^6) * h^(d+1) / ((d+1).factorial : ℝ) := by
  apply psiPanel_error_le hh
  intro x hx
  simpa only [Real.norm_eq_abs, psi] using iteratedDeriv_phi_compact_norm_le d
    (ha.trans hx.1) (hx.2.trans hb)

/-- The normalized Taylor expansion of each real Hankel entry of Ψ₁
has an explicit error for the entire cell [c-h,c+h] ⊆ [0,2]. -/
theorem psiOne_jet_cellTaylor_error_le (l d : ℕ) {c h v : ℝ}
    (ha : 0 ≤ c-h) (hb : c+h ≤ 2) (hh : 0 ≤ h) (hv : |v| ≤ 1) :
    |iteratedDeriv l (psi 1) (c+h*v) -
      cellTaylor (iteratedDeriv l (psi 1)) d c h v| ≤
      ((((d+l).factorial : ℝ) * 8^(d+l)) * 10^6) * h^(d+1) / ((d+1).factorial : ℝ) := by
  apply cellTaylor_error_le ((contDiff_psi_jet 1 l).of_le (by simp)) hh hv (by positivity)
  intro x hx
  have he : d+1+l = (d+l)+1 := by omega
  rw [show iteratedDeriv (d+1) (iteratedDeriv l (psi 1)) =
    iteratedDeriv (d+1+l) (psi 1) from iteratedDeriv_iteratedDeriv_eq _ _ _, he,
    show (1:ℕ) = 0+1 by rfl, iteratedDeriv_succ_psi_succ, abs_neg]
  simpa only [Real.norm_eq_abs, psi] using iteratedDeriv_phi_compact_norm_le (d+l)
    (ha.trans hx.1) (hx.2.trans hb)

/-- The omitted Taylor terms of every scaled Hankel entry in the first
rank-seven cell contribute at most 10⁻¹⁹ before its congruence. -/
theorem psiOne_first_cell_scaled_error_le (l : ℕ) (hl : l ≤ 12) {v : ℝ} (hv : |v| ≤ 1) :
    |(1/16:ℝ)^l *
      (iteratedDeriv l (psi 1) (1/256 + (1/256)*v) -
        cellTaylor (iteratedDeriv l (psi 1)) 24 (1/256) (1/256) v)| ≤ (1:ℝ)/10^19 := by
  have h := psiOne_jet_cellTaylor_error_le l 24 (c := 1/256) (h := 1/256)
    (by norm_num) (by norm_num) (by norm_num) hv
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1/16:ℝ)^l)]
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  interval_cases l <;> norm_num [Nat.factorial]

#print axioms psiOne_panel_error_le
#print axioms psiOne_first_cell_scaled_error_le

end Nuttall
