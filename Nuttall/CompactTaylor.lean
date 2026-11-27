import Mathlib.Analysis.Calculus.Taylor

namespace Nuttall

open Set
open scoped BigOperators

/-- The Taylor polynomial in a normalized cell coordinate. -/
noncomputable def cellTaylor (f : ℝ → ℝ) (d : ℕ) (c h v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1), (iteratedDeriv k f c * h^k / (k.factorial : ℝ)) * v^k

theorem taylorWithinEval_eq_cellTaylor {f : ℝ → ℝ} {d : ℕ} {c h v : ℝ}
    (hf : ContDiff ℝ (d + 1 : ℕ) f) (he : c ≠ c+h*v) :
    taylorWithinEval f d (uIcc c (c+h*v)) c (c+h*v) = cellTaylor f d c h v := by
  have hcMem : c ∈ uIcc c (c+h*v) := left_mem_uIcc
  simp only [taylor_within_apply, cellTaylor, smul_eq_mul, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d + 1 := by have := Finset.mem_range.mp hk; omega
  have hD : ContDiffAt ℝ (k : ℕ) f c := (hf.of_le (by exact_mod_cast hk')).contDiffAt
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc he) hD hcMem, mul_pow]
  ring

/-- A uniform bound on the first omitted derivative gives a Taylor enclosure
on a closed cell, including its center and both ends. -/
theorem cellTaylor_error_le {f : ℝ → ℝ} {d : ℕ} {c h v C : ℝ}
    (hf : ContDiff ℝ (d + 1 : ℕ) f) (hh : 0 ≤ h) (hv : |v| ≤ 1)
    (hC : 0 ≤ C)
    (hDeriv : ∀ x ∈ Icc (c-h) (c+h), |iteratedDeriv (d + 1) f x| ≤ C) :
    |f (c+h*v) - cellTaylor f d c h v| ≤ C * h^(d+1) / ((d+1).factorial : ℝ) := by
  have hd : |h * v| ≤ h := by
    simpa only [abs_mul, abs_of_nonneg hh, mul_one] using mul_le_mul_of_nonneg_left hv hh
  have hx : c+h*v ∈ Icc (c-h) (c+h) := by
    obtain ⟨hl, hu⟩ := abs_le.mp hd
    exact ⟨by linarith only [hl], by linarith only [hu]⟩
  by_cases he : c = c+h*v
  · have hhv : h*v = 0 := by linarith only [he]
    have hPoly : cellTaylor f d c h v = f c := by
      unfold cellTaylor
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk
        calc
          _ = (iteratedDeriv k f c / (k.factorial : ℝ)) * (h*v)^k := by rw [mul_pow]; ring
          _ = 0 := by rw [hhv, zero_pow hk, mul_zero]
      · simp
    rw [hPoly, ← he, sub_self, abs_zero]
    positivity
  obtain ⟨x, hx', hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv he hf.contDiffOn
  have hp := taylorWithinEval_eq_cellTaylor hf he
  have hsub : uIcc c (c+h*v) ⊆ Icc (c-h) (c+h) := by
    exact uIcc_subset_Icc ⟨by linarith only [hh], by linarith only [hh]⟩ hx
  rw [hp, add_sub_cancel_left] at hrem
  rw [hrem, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  exact div_le_div_of_nonneg_right
    (mul_le_mul (hDeriv x (hsub (uIoo_subset_uIcc_self hx')))
      (pow_le_pow_left₀ (abs_nonneg _) hd _) (pow_nonneg (abs_nonneg _) _) hC) (by positivity)

#print axioms cellTaylor_error_le

end Nuttall
