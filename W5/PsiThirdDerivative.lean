import W5.PhiSecondDerivative
import W5.PsiFundamentalDerivative

/-!
# Genuine third derivative of the original theta primitive

From the fundamental theorem Psi1' = -Phi and the proved second
derivative of Phi, derive Psi1''' = -sum of second theta-summand
derivatives. We give a HasDerivAt statement as well as a value
identity, with no assumed theta transformation correctness.
-/

namespace W5

/-- The original Psi1 has a genuine third derivative at every t. -/
theorem Psi1_second_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 2 Psi1)
      (-(∑' n : ℕ, phiSummandSecondDerivative n t)) t := by
  have htwo : iteratedDeriv 2 Psi1 =
      fun s : ℝ => -(deriv Phi s) := by
    funext s
    rw [Psi1_second_derivative, (Phi_hasDerivAt s).deriv]
  rw [htwo]
  exact (Phi_deriv_hasDerivAt t).neg

/-- Exact third derivative of the genuine integrated theta kernel. -/
theorem Psi1_third_derivative (t : ℝ) :
    iteratedDeriv 3 Psi1 t =
      -(∑' n : ℕ, phiSummandSecondDerivative n t) := by
  rw [show (3:ℕ)=2+1 by omega, iteratedDeriv_succ]
  exact (Psi1_second_hasDerivAt t).deriv

/-- The second derivative of the original Psi1 is differentiable
everywhere; no conditional theta matrix assumption is needed. -/
theorem Psi1_second_differentiable :
    Differentiable ℝ (iteratedDeriv 2 Psi1) := by
  intro t
  exact (Psi1_second_hasDerivAt t).differentiableAt

end W5
