import Nuttall.PhiCompactReplay
import Nuttall.PhiFarSign

namespace Nuttall

/-- Strict signed Wronskians through rank four for the original theta kernel. -/
theorem signRegularWronskians_zero_four_of_compact_check
    (hgrid : phiCompactGridChecked) : signRegularWronskians 0 4 := by
  intro p hp₁ hp₄ t ht
  have he := Real.one_le_exp (by linarith : 0 ≤ 4*t)
  have hX : 3 ≤ phiThetaCoordinate t := by
    unfold phiThetaCoordinate
    exact Real.pi_gt_three.le.trans
      (by simpa using mul_le_mul_of_nonneg_left he Real.pi_pos.le)
  change 0 < kernelMinorSign p * wronskian W5.Phi p t
  by_cases h : phiThetaCoordinate t ≤ 16
  · exact phiCompactWronskian_pos hgrid hp₁ hp₄ t hX h
  · exact phiFarWronskian_pos hp₄ t (le_of_not_ge h)

/-- Zero integrations suffice up to rank four in the preprint's weak convention. -/
theorem kernelIntegrationOrder_eq_zero_of_le_four_of_compact_check
    (hgrid : phiCompactGridChecked) {r : ℕ} (hr : r ≤ 4) :
    kernelIntegrationOrder r = 0 := by
  have h := (signRegularWronskians_zero_four_of_compact_check hgrid).strictReverseSignRegular.reverseSignRegular
  exact le_antisymm (kernelIntegrationOrder_le_of_reverseSignRegular (h.mono hr)) zero_le

/-- The original kernel has the strict signed Wronskians through rank four
on the entire nonnegative half-line. -/
theorem signRegularWronskians_zero_four : signRegularWronskians 0 4 :=
  signRegularWronskians_zero_four_of_compact_check phiCompactGridChecked_proved

/-- The minimum is zero for every rank up to four. -/
theorem kernelIntegrationOrder_eq_zero_of_le_four {r : ℕ} (hr : r ≤ 4) :
    kernelIntegrationOrder r = 0 :=
  kernelIntegrationOrder_eq_zero_of_le_four_of_compact_check phiCompactGridChecked_proved hr

#print axioms kernelIntegrationOrder_eq_zero_of_le_four

#print axioms signRegularWronskians_zero_four_of_compact_check
#print axioms kernelIntegrationOrder_eq_zero_of_le_four_of_compact_check

end Nuttall
