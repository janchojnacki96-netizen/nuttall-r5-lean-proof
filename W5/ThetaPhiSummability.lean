import W5.ThetaGaussianSummability
import W5.Statement

/-!
# Actual convergence of the theta series defining Phi

This proves unconditional termwise summability for every real t.
Previously `Phi t` was syntactically defined by a `tsum` without
a proof that the sum converges. This module closes that gap.
It does *not* justify integration of the sum over an unbounded interval.
-/

namespace W5

theorem phiSummand_zero (t : ℝ) : phiSummand 0 t = 0 := by
  simp [phiSummand]

theorem phiSummand_summable (t : ℝ) :
    Summable (fun n : ℕ => phiSummand n t) := by
  let a : ℝ := Real.pi * Real.exp (4*t)
  have ha : 0 < a := mul_pos Real.pi_pos (Real.exp_pos _)
  have heq (n : ℕ) :
      -a * (n:ℝ)^2 =
      -(n:ℝ)^2 * Real.pi * Real.exp (4*t) := by
    dsimp [a]
    ring
  have h4 : Summable (fun n : ℕ =>
      (n:ℝ)^4 * Real.exp (-(n:ℝ)^2 * Real.pi * Real.exp (4*t))) := by
    simpa only [heq] using
      theta_gaussian_polynomial_summable 4 a ha
  have h2 : Summable (fun n : ℕ =>
      (n:ℝ)^2 * Real.exp (-(n:ℝ)^2 * Real.pi * Real.exp (4*t))) := by
    simpa only [heq] using
      theta_gaussian_polynomial_summable 2 a ha
  have hsum :=
    (h4.mul_left (2 * Real.pi^2 * Real.exp (9*t))).sub
      (h2.mul_left (3 * Real.pi * Real.exp (5*t)))
  convert hsum using 1
  funext n
  unfold phiSummand
  ring

theorem Phi_eq_tsum_phiSummand (t : ℝ) :
    Phi t = ∑' n : ℕ, phiSummand n t := by
  unfold Phi
  congr 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp [phiSummand_zero]
  · simp [hn]

end W5
