import Nuttall.ReverseSignRegularity
import Nuttall.ShiftRelativeTailProof

namespace Nuttall

open Filter

/-- The integration level (2r) verifies all strict kernel signs for
sufficiently large (r). -/
theorem eventually_strictReverseSignRegular_psi_two_mul :
    ∀ᶠ r : ℕ in atTop, strictReverseSignRegular (psi (2*r)) r := by
  filter_upwards [eventually_signRegularWronskians_two_mul] with r hr
  exact hr.strictReverseSignRegular

/-- Every prescribed order has a successful integration level. This is the
existence result in the weak reverse sign convention of the preprint. -/
theorem exists_reverseSignRegular_psi (r : ℕ) :
    ∃ m : ℕ, reverseSignRegular (psi m) r := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 eventually_strictReverseSignRegular_psi_two_mul
  let R := max r R₀
  exact ⟨2*R, (hR₀ R (le_max_right _ _)).reverseSignRegular.mono (le_max_left _ _)⟩

/-- The analytic asymptotic upper bound (m(r) \le 2r), with (m(r))
defined via all weakly signed kernel minors. -/
theorem eventually_kernelIntegrationOrder_le_two_mul :
    ∀ᶠ r : ℕ in atTop, kernelIntegrationOrder r ≤ ((2*r : ℕ) : ℕ∞) := by
  filter_upwards [eventually_strictReverseSignRegular_psi_two_mul] with r hr
  exact kernelIntegrationOrder_le_of_reverseSignRegular hr.reverseSignRegular

/-- The infimum of successful levels is finite and attained for every rank. -/
theorem kernelIntegrationOrder_attained (r : ℕ) :
    ∃ m : ℕ, kernelIntegrationOrder r = m ∧ reverseSignRegular (psi m) r := by
  exact kernelIntegrationOrder_attained_of_exists (exists_reverseSignRegular_psi r)

#print axioms exists_reverseSignRegular_psi
#print axioms eventually_kernelIntegrationOrder_le_two_mul
#print axioms kernelIntegrationOrder_attained

end Nuttall
