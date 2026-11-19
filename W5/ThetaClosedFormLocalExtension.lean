import W5.ThetaDensityClosedForm
import W5.ThetaGaussianUniformDecay

/-!
# Closed theta series on a neighborhood of the original t >= 0 ray

The existing proof `Psi1_eq_theta_closed_form` covers t >= 0, but
local differentiation at t=0 requires the closed form at nearby
slightly negative t as well. Its proof actually only needs
  1 <= pi * exp (4*t)
for the y-tail Fubini theorem.

This module lifts the real analytic identity to that larger open
region and proves it remains valid on a concrete two-variable
neighborhood of every point t>=0, including the endpoint t=0.
The derivative/integral interchange is NOT claimed here.
-/

namespace W5
open MeasureTheory

/-- Exact theta series appearing in the closed form of the ORIGINAL
Psi1, not an independent new definition of the original function. -/
noncomputable def psiThetaClosedSeries (t : ℝ) : ℝ :=
  (1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) *
    (∑' n : ℕ,
      2 * (n:ℝ)^2 *
        (Real.pi * Real.exp (4*t)) ^ ((5:ℝ)/4) *
          (Real.exp (-(n:ℝ)^2 * (Real.pi * Real.exp (4*t))) -
            (1/4:ℝ) *
              (∫ v in Set.Ioi (1:ℝ),
                v ^ ((1:ℝ)/4) *
                  Real.exp (-(n:ℝ)^2 *
                    (Real.pi * Real.exp (4*t))*v))))

/-- Stronger domain than t>=0: the closed theta representation
is valid whenever the corresponding y-coordinate is >= 1. -/
theorem Psi1_eq_psiThetaClosedSeries_of_y_ge_one
    (t : ℝ) (hy : 1 ≤ Real.pi * Real.exp (4*t)) :
    Psi1 t = psiThetaClosedSeries t := by
  have hclosed :
      (∫ y in Set.Ioi (Real.pi * Real.exp (4*t)),
        ∑' n : ℕ, thetaYIntegrand n y) =
      ∑' n : ℕ,
        2 * (n:ℝ)^2 *
          (Real.pi * Real.exp (4*t)) ^ ((5:ℝ)/4) *
            (Real.exp (-(n:ℝ)^2 * (Real.pi * Real.exp (4*t))) -
             (1/4:ℝ) *
               (∫ v in Set.Ioi (1:ℝ),
                 v ^ ((1:ℝ)/4) *
                   Real.exp (-(n:ℝ)^2 *
                     (Real.pi * Real.exp (4*t))*v))) := by
    simpa only [MeasureTheory.integral_Ici_eq_integral_Ioi] using
      (thetaY_integral_tsum_closed_form
        (Real.pi * Real.exp (4*t)) hy)
  rw [Psi1_eq_thetaY_integral, hclosed]
  rfl

/-- The transformed y-coordinate remains >=1 in an actual
two-variable neighborhood of each t >= 0. This handles the
border t=0, where assuming the shifted time is nonnegative fails. -/
theorem theta_local_shift_y_ge_one (t x u v : ℝ)
    (ht : 0 ≤ t)
    (hu : -(1:ℝ)/4 ≤ x*u)
    (hv : -(1:ℝ)/4 ≤ x*v) :
    1 ≤ Real.pi *
      Real.exp (4*(t + Real.log (1+x*u)/4 +
        Real.log (1+x*v)/4)) := by
  have hxu : (3:ℝ)/4 ≤ 1+x*u := by linarith
  have hxv : (3:ℝ)/4 ≤ 1+x*v := by linarith
  have hupos : 0 < 1+x*u := by linarith
  have hvpos : 0 < 1+x*v := by linarith
  have hprod : (9:ℝ)/16 ≤ (1+x*u)*(1+x*v) := by
    calc
      (9:ℝ)/16 = (3/4:ℝ)*(3/4:ℝ) := by norm_num
      _ ≤ (1+x*u)*(1+x*v) :=
        mul_le_mul hxu hxv (by norm_num) (by linarith)
  have h4t : 0 ≤ (4:ℝ)*t := by linarith
  have hexp : (1:ℝ) ≤ Real.exp (4*t) := by
    linarith [Real.add_one_le_exp (4*t)]
  have hbase : (3:ℝ) ≤ Real.pi * Real.exp (4*t) := by
    calc
      (3:ℝ) = 3*1 := by ring
      _ ≤ Real.pi * Real.exp (4*t) :=
        mul_le_mul (le_of_lt Real.pi_gt_three) hexp
          (by norm_num) (le_of_lt Real.pi_pos)
  have hshift :
      Real.exp (4*(t + Real.log (1+x*u)/4 +
          Real.log (1+x*v)/4)) =
        Real.exp (4*t) * (1+x*u) * (1+x*v) := by
    calc
      _ = Real.exp ((4*t + Real.log (1+x*u)) +
          Real.log (1+x*v)) := by congr 1; ring
      _ = Real.exp (4*t) * (1+x*u) * (1+x*v) := by
        rw [Real.exp_add, Real.exp_add,
          Real.exp_log hupos, Real.exp_log hvpos]
  calc
    (1:ℝ) ≤ 3 * (9/16:ℝ) := by norm_num
    _ ≤ (Real.pi * Real.exp (4*t)) *
          ((1+x*u)*(1+x*v)) :=
      mul_le_mul hbase hprod (by norm_num)
        (le_of_lt (mul_pos Real.pi_pos (Real.exp_pos _)))
    _ = Real.pi *
          Real.exp (4*(t + Real.log (1+x*u)/4 +
            Real.log (1+x*v)/4)) := by rw [hshift]; ring

/-- The original Psi1 has the exact closed theta series on the
local two-variable patch needed for differentiation of its
normalized kernel at every t>=0. -/
theorem Psi1_eq_closed_theta_series_on_local_patch
    (t x u v : ℝ) (ht : 0 ≤ t)
    (hu : -(1:ℝ)/4 ≤ x*u)
    (hv : -(1:ℝ)/4 ≤ x*v) :
    Psi1 (t + Real.log (1+x*u)/4 + Real.log (1+x*v)/4) =
      psiThetaClosedSeries
        (t + Real.log (1+x*u)/4 + Real.log (1+x*v)/4) :=
  Psi1_eq_psiThetaClosedSeries_of_y_ge_one _
    (theta_local_shift_y_ge_one t x u v ht hu hv)

end W5
