import W5.ThetaDensityClosedForm
import W5.ThetaCoordinateAlgebra

/-!
# Differentiation bridge: exact derivatives of the theta coordinates

This module isolates derivative identities that will be used to
differentiate the theta representation termwise. It does NOT
interchange a derivative with an infinite sum or improper integral.
-/

namespace W5

/-- The exponential coordinate has the expected derivative. -/
theorem theta_y_derivative (t : ℝ) :
    deriv (fun s : ℝ => Real.pi * Real.exp (4*s)) t =
      4 * Real.pi * Real.exp (4*t) :=
  (theta_y_hasDerivAt t).deriv

/-- The reciprocal-square-root coordinate x(t) has derivative -2*x(t).
This identity is a prerequisite for transforming derivatives from t
to the normalized certificate variable x. -/
theorem xOfT_hasDerivAt (t : ℝ) :
    HasDerivAt xOfT (-2 * xOfT t) t := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have he : 0 < Real.exp (4*t) := Real.exp_pos _
  have harg : 0 < Real.pi * Real.exp (4*t) := mul_pos hpi he
  have hlin : HasDerivAt (fun s : ℝ => (4:ℝ)*s) 4 t := by
    simpa using (hasDerivAt_id t).const_mul (4:ℝ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (4*s))
      (Real.exp (4*t)*4) t :=
    (Real.hasDerivAt_exp (4*t)).comp t hlin
  have hpow : HasDerivAt
      (fun s : ℝ => (Real.pi * Real.exp (4*s)) ^ (-(1:ℝ)/2))
      ((-(1:ℝ)/2) *
        (Real.pi * Real.exp (4*t)) ^ (-(1:ℝ)/2-1) *
          (Real.pi * (Real.exp (4*t)*4))) t := by
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt harg))).comp t
      (hexp.const_mul Real.pi)
  have hfun : xOfT =
      (fun s : ℝ => (Real.pi * Real.exp (4*s)) ^ (-(1:ℝ)/2)) := by
    funext s
    unfold xOfT
    rw [Real.sqrt_eq_rpow]
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring]
    simpa only [one_div] using
      (Real.rpow_neg
        (le_of_lt (mul_pos Real.pi_pos (Real.exp_pos (4*s))))
        ((1:ℝ)/2)).symm
  have hs :
      ((-(1:ℝ)/2) *
        (Real.pi * Real.exp (4*t)) ^ (-(1:ℝ)/2-1) *
          (Real.pi * (Real.exp (4*t)*4))) =
        -2 * (Real.pi * Real.exp (4*t)) ^ (-(1:ℝ)/2) := by
    rw [Real.rpow_sub harg, Real.rpow_one]
    field_simp [ne_of_gt harg] <;> ring
  rw [hfun]
  simpa only [hs] using hpow

end W5
