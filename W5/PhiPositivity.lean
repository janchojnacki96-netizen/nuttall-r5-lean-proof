import W5.ThetaPhiSummability
import W5.ThetaCoordinateAlgebra

/-!
# Positivity of the original Riemann theta kernel on the nonnegative half-line

This proves strict positivity of every nonzero theta summand and of its
convergent infinite sum. It is a genuine theorem about the original
`W5.Phi`, not about the interval certificate or a surrogate function.

The passage from `Phi > 0` to `Psi1 > 0` still needs an analytic
integrability/positivity bridge and is NOT asserted here.
-/

namespace W5

theorem phiSummand_pos_of_nonzero (n : ℕ) (t : ℝ)
    (hn : n ≠ 0) (ht : 0 ≤ t) :
    0 < phiSummand n t := by
  have hn1 : 1 ≤ n := by omega
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hp : (1 : ℝ) ≤ (n : ℝ)^2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have he : (1 : ℝ) ≤ Real.exp (4*t) := by
    have hnonneg : (0 : ℝ) ≤ 4*t := by positivity
    simpa using (Real.exp_le_exp.mpr hnonneg :
      Real.exp 0 ≤ Real.exp (4*t))
  have hprod : (1 : ℝ) ≤ (n : ℝ)^2 * Real.exp (4*t) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (n : ℝ)^2 * Real.exp (4*t) :=
        mul_le_mul hp he (by norm_num) (by positivity)
  have hmul : Real.pi ≤ (n : ℝ)^2 * Real.pi * Real.exp (4*t) := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by ring
      _ ≤ ((n : ℝ)^2 * Real.exp (4*t)) * Real.pi :=
        mul_le_mul_of_nonneg_right hprod (le_of_lt Real.pi_pos)
      _ = (n : ℝ)^2 * Real.pi * Real.exp (4*t) := by ring
  have hgap :
      0 < 2 * (n : ℝ)^2 * Real.pi * Real.exp (4*t) - 3 := by
    nlinarith [Real.pi_gt_three]
  rw [phiSummand_factor]
  have hfirst : 0 < (n : ℝ)^2 * Real.pi * Real.exp (5*t) :=
    mul_pos
      (mul_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp)
        Real.pi_pos)
      (Real.exp_pos _)
  exact mul_pos (mul_pos hfirst hgap) (Real.exp_pos _)

theorem phiSummand_nonneg_of_nonneg (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ phiSummand n t := by
  by_cases hn : n = 0
  · subst n
    simp [phiSummand_zero]
  · exact (phiSummand_pos_of_nonzero n t hn ht).le

/-- Strict positivity of the original theta kernel for every t >= 0. -/
theorem Phi_pos (t : ℝ) (ht : 0 ≤ t) : 0 < Phi t := by
  rw [Phi_eq_tsum_phiSummand]
  exact (phiSummand_summable t).tsum_pos
    (fun n => phiSummand_nonneg_of_nonneg n t ht)
    1 (phiSummand_pos_of_nonzero 1 t (by decide) ht)

end W5
