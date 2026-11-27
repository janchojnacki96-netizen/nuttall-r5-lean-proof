import Nuttall.ReverseSignRegularity
import W5.PhiPositivity

namespace Nuttall

/-- The original theta kernel is already strictly reverse sign regular at rank one. -/
theorem strictReverseSignRegular_phi_one : strictReverseSignRegular W5.Phi 1 := by
  intro p hp hpr x y _ _ hx hy
  have hp₁ : p = 1 := by omega
  subst p
  simpa [kernelMinorSign, Matrix.det_fin_one] using W5.Phi_pos (x 0 + y 0) (add_pos (hx 0) (hy 0)).le

theorem kernelIntegrationOrder_one_eq_zero : kernelIntegrationOrder 1 = 0 := by
  have h : reverseSignRegular (psi 0) 1 := strictReverseSignRegular_phi_one.reverseSignRegular
  exact le_antisymm (kernelIntegrationOrder_le_of_reverseSignRegular h) zero_le

#print axioms kernelIntegrationOrder_one_eq_zero

end Nuttall
