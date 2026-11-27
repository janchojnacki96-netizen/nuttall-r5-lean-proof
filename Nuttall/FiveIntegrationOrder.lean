import Nuttall.PhiOriginCertificate
import Nuttall.WronskianObstruction

namespace Nuttall

/-- At every rank from five onward, the unintegrated theta kernel fails the weak condition. -/
theorem one_le_kernelIntegrationOrder_of_five_le {r : ℕ} (hr : 5 ≤ r) :
    1 ≤ kernelIntegrationOrder r :=
  kernelIntegrationOrder_succ_le_of_negative_wronskian (m := 0) (p := 5) (t := 0)
    (by decide) hr le_rfl (by
      norm_num [kernelMinorSign, psi]
      exact phi_origin_wronskian_neg)

/-- The lower bound is certified independently of the rank-five positive replay. -/
theorem kernelIntegrationOrder_five_eq_one_of_mainClaim (h : W5.MainClaim) :
    kernelIntegrationOrder 5 = 1 :=
  kernelIntegrationOrder_five_eq_one_of_witnesses h phi_origin_wronskian_neg

#print axioms one_le_kernelIntegrationOrder_of_five_le
#print axioms kernelIntegrationOrder_five_eq_one_of_mainClaim

end Nuttall
