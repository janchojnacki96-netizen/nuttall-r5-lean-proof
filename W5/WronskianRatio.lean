import W5.PsiThirdDerivative
import W5.ThetaIntegralStrictPositivity

/-!
# The exact second Wronskian as a logarithmic-slope derivative

For the ORIGINAL Riemann theta tail Psi1, the sign of W2 is
equivalent to strict increase of Phi/Psi1. This is a genuine
analytic reduction, not a numerical surrogate or a sign assumption.
-/

namespace W5

/-- The ratio Phi/Psi1 has an explicit derivative wherever Psi1 ≠ 0. -/
theorem Phi_div_Psi1_hasDerivAt (t : ℝ) (hpsi : Psi1 t ≠ 0) :
    HasDerivAt (fun s : ℝ => Phi s / Psi1 s)
      (((∑' n : ℕ, phiSummandDerivative n t) * Psi1 t +
        (Phi t)^2) / (Psi1 t)^2) t := by
  have h := (Phi_hasDerivAt t).div (Psi1_hasDerivAt t) hpsi
  convert h using 1
  ring

/-- Exact W2 identity in terms of the derivative of the positive
theta ratio. No conditional matrix bridge is used. -/
theorem W_two_eq_negative_ratio_derivative (t : ℝ)
    (ht : 0 ≤ t) :
    W 2 t = -(Psi1 t)^2 *
      deriv (fun s : ℝ => Phi s / Psi1 s) t := by
  have hpsi : Psi1 t ≠ 0 := ne_of_gt (Psi1_pos t ht)
  rw [(Phi_div_Psi1_hasDerivAt t hpsi).deriv,
      W_two_eq_original_theta_derivatives]
  field_simp [hpsi]
  <;> ring

/-- A sharp analytic equivalence for the genuine order-two sign. -/
theorem W_two_negative_iff_ratio_deriv_pos (t : ℝ)
    (ht : 0 ≤ t) :
    W 2 t < 0 ↔
      0 < deriv (fun s : ℝ => Phi s / Psi1 s) t := by
  rw [W_two_eq_negative_ratio_derivative t ht]
  have hs : 0 < (Psi1 t)^2 := sq_pos_of_pos (Psi1_pos t ht)
  constructor
  · intro h
    have hprod : 0 < (Psi1 t)^2 *
        deriv (fun s : ℝ => Phi s / Psi1 s) t := by
      linarith
    exact (mul_pos_iff_of_pos_left hs).mp hprod
  · intro h
    exact neg_mul_neg_iff.mpr (mul_pos hs h)

end W5
