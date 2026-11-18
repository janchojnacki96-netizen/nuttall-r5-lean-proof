import W5.ThetaIntegratedClosedForm
import W5.ThetaCoordinateAlgebra
import W5.PhiPositivity

/-!
# Original t-variable theta summands and the y-variable series

This identifies the original `phiSummand` with the exact y-coordinate
integrand at `y = pi * exp (4*t)`, including the full density factor.
It is a *pointwise* identity. The next analytic task is to use the
Jacobian and integrate it on the half-line.

A second result proves nonnegativity of the original integrated
kernel `Psi1` for nonnegative t. Strict positivity is still an
independent goal.
-/

namespace W5

open MeasureTheory

theorem phiSummand_eq_thetaYIntegrand (n : ℕ) (t : ℝ) :
    phiSummand n t =
      (Real.pi * Real.exp (5*t) /
          (Real.pi * Real.exp (4*t)) ^ ((1 : ℝ)/4)) *
        thetaYIntegrand n (Real.pi * Real.exp (4*t)) := by
  have hypos : 0 < Real.pi * Real.exp (4*t) :=
    mul_pos Real.pi_pos (Real.exp_pos _)
  have hyquarter : 0 <
      (Real.pi * Real.exp (4*t)) ^ ((1 : ℝ)/4) :=
    Real.rpow_pos_of_pos hypos _
  rw [phiSummand_factor]
  dsimp [thetaYIntegrand]
  have harg :
      -(n : ℝ)^2 * (Real.pi * Real.exp (4*t)) =
        -(n : ℝ)^2 * Real.pi * Real.exp (4*t) := by ring
  rw [harg]
  field_simp [ne_of_gt hyquarter]
  ring

/-- Unconditional pointwise identity between the two infinite theta series. -/
theorem Phi_eq_thetaY_tsum (t : ℝ) :
    Phi t =
      (Real.pi * Real.exp (5*t) /
        (Real.pi * Real.exp (4*t)) ^ ((1 : ℝ)/4)) *
        (∑' n : ℕ, thetaYIntegrand n (Real.pi * Real.exp (4*t))) := by
  rw [Phi_eq_tsum_phiSummand]
  simp_rw [phiSummand_eq_thetaYIntegrand]
  rw [tsum_mul_left]

/-- Nonnegativity of the actual integrated kernel on t >= 0.
Strict positivity requires a separate positive-integral argument. -/
theorem Psi1_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ Psi1 t := by
  unfold Psi1
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ici
  intro s hs
  exact (Phi_pos s (le_trans ht hs)).le

end W5
