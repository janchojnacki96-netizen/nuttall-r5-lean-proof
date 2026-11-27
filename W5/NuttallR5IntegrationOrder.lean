import Nuttall.FiveIntegrationOrder
import W5.NuttallR5

/-! This target also imports the archived rank-five positive certificate.
Build it separately to retain the incremental workflow for the analytic preprint. -/

namespace Nuttall

/-- Exactly one integration is needed for rank five in the preprint's weak convention. -/
theorem kernelIntegrationOrder_five_eq_one : kernelIntegrationOrder 5 = 1 :=
  kernelIntegrationOrder_five_eq_one_of_mainClaim W5.nuttall_r5

#print axioms kernelIntegrationOrder_five_eq_one

end Nuttall
