import W5.ThetaWronskianCoordinate
import W5.Range

/-!
# An explicit inverse theta coordinate for the ORIGINAL Psi1

The previous determinant-coordinate theorem requested an abstract
representation Psi1(t) = f(xOfT t). Here we supply an explicit f
using the inverse coordinate t(x) = log((1/x^2)/pi)/4 and discharge
that representation premise by a real-variable identity.

Smoothness of the resulting function and its derivatives remains an
explicit, not-yet-established hypothesis for the Wronskian identity.
This file does not assert the order-five sign conjecture.
-/

namespace W5

/-- Inverse theta coordinate (defined algebraically on all real x). -/
noncomputable def thetaTimeOfX (x : ℝ) : ℝ :=
  Real.log ((1 / x^2) / Real.pi) / 4

/-- The inverse theta coordinate recovers EVERY real t, not only t ≥ 0. -/
theorem thetaTimeOfX_xOfT (t : ℝ) :
    thetaTimeOfX (xOfT t) = t := by
  have hy : 0 < Real.pi * Real.exp (4*t) :=
    mul_pos Real.pi_pos (Real.exp_pos _)
  have hsqr :
      (Real.sqrt (Real.pi * Real.exp (4*t)))^2 =
        Real.pi * Real.exp (4*t) :=
    Real.sq_sqrt (le_of_lt hy)
  have hs : Real.sqrt (Real.pi * Real.exp (4*t)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hy)
  have hval :
      1 / (xOfT t)^2 = Real.pi * Real.exp (4*t) := by
    unfold xOfT
    calc
      1 / (1 / Real.sqrt (Real.pi * Real.exp (4*t)))^2 =
          (Real.sqrt (Real.pi * Real.exp (4*t)))^2 := by
            field_simp [hs]
      _ = Real.pi * Real.exp (4*t) := hsqr
  have hquot :
      ((1 / (xOfT t)^2) / Real.pi) = Real.exp (4*t) := by
    rw [hval]
    field_simp [ne_of_gt Real.pi_pos]
  unfold thetaTimeOfX
  rw [hquot, Real.log_exp]
  ring

/-- Psi1 expressed in the explicit x-coordinate. No representation
assumption is required, since the inverse composition is proved. -/
noncomputable def psiThetaCoordinate (x : ℝ) : ℝ :=
  Psi1 (thetaTimeOfX x)

theorem psiThetaCoordinate_comp_xOfT (t : ℝ) :
    psiThetaCoordinate (xOfT t) = Psi1 t := by
  simp [psiThetaCoordinate, thetaTimeOfX_xOfT]

/-- The ORIGINAL Wronskian matrix has the x-operator representation,
conditional ONLY on differentiability of the explicit theta-coordinate
function, not on any abstract representation identity. -/
theorem W_eq_thetaWronskian_explicit
    (r : ℕ)
    (hf : ∀ k < 2*r,
      Differentiable ℝ ((thetaDerivOp^[k]) psiThetaCoordinate))
    (t : ℝ) :
    W r t = thetaWronskian r psiThetaCoordinate (xOfT t) := by
  apply W_eq_thetaWronskian_of_representation r psiThetaCoordinate
  · intro s
    exact (psiThetaCoordinate_comp_xOfT s).symm
  · exact hf
  · exact t

/-- Explicit order-five determinant identity. It needs smoothness
through the eighth derivative of psiThetaCoordinate, which remains
a separate mathematical obligation. -/
theorem W_five_eq_thetaWronskian_explicit
    (hf : ∀ k < 9,
      Differentiable ℝ ((thetaDerivOp^[k]) psiThetaCoordinate))
    (t : ℝ) :
    W 5 t = thetaWronskian 5 psiThetaCoordinate (xOfT t) := by
  apply W_five_eq_thetaWronskian psiThetaCoordinate
  · intro s
    exact (psiThetaCoordinate_comp_xOfT s).symm
  · exact hf
  · exact t

end W5
