import W5.PhiPositivity
import W5.ThetaOriginalCoordinate
import W5.ThetaIteratedChainRule

/-!
# Exact low-order Wronskians of the original Riemann theta primitive

These are identities for the actual W5.W, not the numerical surrogate
or a substituted coefficient matrix. The first-order result yields
an unconditional NONNEGATIVE sign for W1 on t >= 0.

The strict sign W1 > 0 requires a separate integrability and
strict-positive-integral argument, and remains explicitly open here.
-/

namespace W5

/-- The order-one Wronskian is precisely the original integral kernel. -/
theorem W_one_eq_Psi1 (t : ℝ) : W 1 t = Psi1 t := by
  simp [W, Matrix.det_fin_one]

/-- The first unconditional Wronskian sign: nonnegativity on t >= 0. -/
theorem W_one_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ W 1 t := by
  rw [W_one_eq_Psi1]
  exact Psi1_nonneg t ht

/-- The exact order-two Wronskian, expanded with the 2x2 determinant formula. -/
theorem W_two_eq_derivatives (t : ℝ) :
    W 2 t =
      Psi1 t * iteratedDeriv 2 Psi1 t -
        (deriv Psi1 t)^2 := by
  simp [W, Matrix.det_fin_two, iteratedDeriv_one, iteratedDeriv_zero]
  ring

/-- The second desired sign is exactly a strict curvature condition
on the original Psi1; neither direction is assumed. -/
theorem W_two_negative_iff (t : ℝ) :
    W 2 t < 0 ↔
      Psi1 t * iteratedDeriv 2 Psi1 t < (deriv Psi1 t)^2 := by
  rw [W_two_eq_derivatives]
  constructor <;> intro h <;> nlinarith

end W5
