import W5.ThetaFiniteBoundaryIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Fully explicit finite-interval integration by parts and vanishing boundary

This is the exact finite-y integral identity needed for the
single-square term of the theta kernel, with no conditional analytic
premises beyond p>0 and 0<a<=b. The exponential-power boundary term
also tends to zero as b tends to +infinity.

The next formal obligation is taking the improper integral limit and
connecting the y-integral to the t-coordinate Psi1.
-/

namespace W5

open MeasureTheory intervalIntegral Filter

theorem theta_finite_integration_by_parts (p a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b,
       y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y) +
       (1/2:ℝ) * y ^ ((1:ℝ)/4) * Real.exp (-p*y)) =
      2*a ^ ((5:ℝ)/4)*Real.exp (-p*a) -
      2*b ^ ((5:ℝ)/4)*Real.exp (-p*b) := by
  have hcongr :
      (∫ y in a..b,
         y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y) +
           (1/2:ℝ) * y ^ ((1:ℝ)/4) * Real.exp (-p*y)) =
      (∫ y in a..b,
         (-2:ℝ) * (((5:ℝ)/4)*y ^ ((1:ℝ)/4)*Real.exp (-p*y) -
              p*y ^ ((5:ℝ)/4)*Real.exp (-p*y))) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hya : a ≤ y := by
      have hy' : y ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab] using hy
      exact hy'.1
    have h := theta_integration_by_parts_integrand p y
      (lt_of_lt_of_le ha hya)
    rw [h]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul,
    theta_boundary_integral_finite p a b ha hab]
  ring

theorem theta_boundary_tendsto_zero (p : ℝ) (hp : 0 < p) :
    Tendsto
      (fun y : ℝ => y ^ ((5:ℝ)/4) * Real.exp (-p*y))
      atTop (nhds 0) := by
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((5:ℝ)/4) p hp

end W5
