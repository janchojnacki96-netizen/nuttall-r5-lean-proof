import W5.PhiTailIntegrability
import W5.WronskianLowOrder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fundamental theorem of calculus for the actual Riemann theta primitive

Using the now-proved tail integrability of Phi on EVERY real
half-line, the ordinary Lebesgue integral defining Psi1 is an
antiderivative of -Phi. This is an unconditional statement about
the original Psi1, not about its theta-coordinate surrogate.

In particular the second derivative is the negative of the
first differentiated theta series, and the genuine order-two
Wronskian can be expressed directly in these terms.

Proving the desired strict NEGATIVE sign for W2 still requires a
separate analytic inequality; it is not deduced here.
-/

namespace W5

open MeasureTheory intervalIntegral

/-- Split the genuine improper theta integral at zero; no assumption
on the sign of t is required. -/
theorem Psi1_eq_zero_tail_sub_interval (t : ℝ) :
    Psi1 t = Psi1 0 - (∫ s in (0:ℝ)..t, Phi s) := by
  have h := intervalIntegral.integral_Ici_sub_Ici'
    (Phi_integrableOn_Ici_all (0:ℝ))
    (Phi_integrableOn_Ici_all t)
  change Psi1 0 - Psi1 t = (∫ s in (0:ℝ)..t, Phi s) at h
  linarith

/-- For ALL real t, the derivative of the original improper
integral Psi1 is exactly minus the original theta function Phi. -/
theorem Psi1_hasDerivAt (t : ℝ) :
    HasDerivAt Psi1 (-Phi t) t := by
  have hc : Continuous Phi := Phi_differentiable.continuous
  have hFTC :
      HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, Phi s)
        (Phi t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 t)
      (hc.aestronglyMeasurable.stronglyMeasurableAtFilter)
      hc.continuousAt
  have hfun :
      (fun u : ℝ => Psi1 0 - (∫ s in (0:ℝ)..u, Phi s)) =
        Psi1 := by
    funext u
    exact (Psi1_eq_zero_tail_sub_interval u).symm
  simpa only [hfun] using hFTC.const_sub (Psi1 0)

/-- The first derivative of Psi1 at any real t. -/
theorem Psi1_deriv (t : ℝ) : deriv Psi1 t = -Phi t :=
  (Psi1_hasDerivAt t).deriv

/-- The second derivative of the genuine Psi1 is the negative of the
verified termwise derivative series. -/
theorem Psi1_second_derivative (t : ℝ) :
    iteratedDeriv 2 Psi1 t =
      -(∑' n : ℕ, phiSummandDerivative n t) := by
  have hfun : deriv Psi1 = (fun s : ℝ => -Phi s) := by
    funext s
    exact Psi1_deriv s
  rw [show (2:ℕ)=1+1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hfun]
  exact (Phi_hasDerivAt t).neg.deriv

/-- Exact formula for the ORIGINAL order-two Wronskian.
The sign is NOT claimed here. -/
theorem W_two_eq_original_theta_derivatives (t : ℝ) :
    W 2 t = -(Psi1 t * (∑' n : ℕ, phiSummandDerivative n t)) -
      (Phi t)^2 := by
  rw [W_two_eq_derivatives, Psi1_second_derivative, Psi1_deriv]
  ring

end W5
