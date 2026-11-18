import W5.ThetaOriginalCoordinate
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact substitution y = pi * exp(4*t) on a half-line

The first theorem is an actual change-of-variables result for ANY
real integrand, with no unproved continuity or integrability hypotheses.
It composes the existing Mathlib substitution lemmas for multiplication
and the exponential function.

The second theorem applies this to the original `Psi1`, using an
explicit inverse-coordinate density. Relating that density to the
closed-form theta series is a subsequent, separate obligation.
-/

namespace W5

open MeasureTheory

/-- Change of variables y = pi * exp(4*s), including its Jacobian. -/
theorem theta_exp_change_variables (g : ℝ → ℝ) (t : ℝ) :
    (∫ s in Set.Ioi t,
      (4 * Real.pi * Real.exp (4*s)) *
        g (Real.pi * Real.exp (4*s))) =
      ∫ y in Set.Ioi (Real.pi * Real.exp (4*t)), g y := by
  let h : ℝ → ℝ := fun u =>
    Real.pi * Real.exp u * g (Real.pi * Real.exp u)
  have hfour :
      (∫ s in Set.Ioi t, (4:ℝ) * h (4*s)) =
        ∫ u in Set.Ioi ((4:ℝ)*t), h u := by
    simpa only [smul_eq_mul] using
      (MeasureTheory.integral_comp_mul_left_Ioi' h t
        (by norm_num : (0:ℝ) < 4))
  have hexp :
      (∫ u in Set.Ioi ((4:ℝ)*t), h u) =
        ∫ v in Set.Ioi (Real.exp (4*t)),
          Real.pi * g (Real.pi*v) := by
    calc
      (∫ u in Set.Ioi ((4:ℝ)*t), h u) =
          ∫ u in Set.Ioi ((4:ℝ)*t),
            Real.exp u * (Real.pi*g (Real.pi*Real.exp u)) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
              intro u hu
              dsimp [h]
              ring
      _ = _ := by
        simpa only [smul_eq_mul] using
          (MeasureTheory.integral_comp_exp_Ioi
            (fun v : ℝ => Real.pi * g (Real.pi*v)) (4*t))
  have hpi :
      (∫ v in Set.Ioi (Real.exp (4*t)),
          Real.pi * g (Real.pi*v)) =
        ∫ y in Set.Ioi (Real.pi * Real.exp (4*t)), g y := by
    calc
      _ = Real.pi * (∫ v in Set.Ioi (Real.exp (4*t)),
            g (Real.pi*v)) := by rw [integral_const_mul]
      _ = _ := by
        simpa only [smul_eq_mul] using
          (MeasureTheory.integral_comp_mul_left_Ioi'
            g (Real.exp (4*t)) Real.pi_pos)
  calc
    (∫ s in Set.Ioi t,
        (4 * Real.pi * Real.exp (4*s)) *
          g (Real.pi * Real.exp (4*s))) =
        ∫ s in Set.Ioi t, (4:ℝ) * h (4*s) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro s hs
          dsimp [h]
          ring
    _ = (∫ u in Set.Ioi ((4:ℝ)*t), h u) := hfour
    _ = (∫ v in Set.Ioi (Real.exp (4*t)),
          Real.pi * g (Real.pi*v)) := hexp
    _ = ∫ y in Set.Ioi (Real.pi * Real.exp (4*t)), g y := hpi

/-- Density of the original integrated theta kernel in the y-coordinate.
The inverse map is t = log(y/pi)/4. -/
noncomputable def thetaOriginalDensity (y : ℝ) : ℝ :=
  (4*y)⁻¹ * Phi (Real.log (y / Real.pi)/4)

theorem thetaOriginalDensity_at_exp (t : ℝ) :
    (4 * Real.pi * Real.exp (4*t)) *
        thetaOriginalDensity (Real.pi * Real.exp (4*t)) =
      Phi t := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have heq :
      (Real.pi * Real.exp (4*t)) / Real.pi =
        Real.exp (4*t) := by
    field_simp
  have ht : (4*t)/4 = t := by ring
  have hden : (4:ℝ)*Real.pi*Real.exp (4*t) ≠ 0 :=
    ne_of_gt (by positivity)
  unfold thetaOriginalDensity
  rw [heq, Real.log_exp, ht]
  field_simp [hden]

/-- Genuine t-to-y substitution in the ORIGINAL integral defining Psi1. -/
theorem Psi1_eq_integral_thetaOriginalDensity (t : ℝ) :
    Psi1 t =
      ∫ y in Set.Ioi (Real.pi * Real.exp (4*t)),
        thetaOriginalDensity y := by
  rw [Psi1]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  calc
    (∫ s in Set.Ioi t, Phi s) =
        ∫ s in Set.Ioi t,
          (4 * Real.pi * Real.exp (4*s)) *
            thetaOriginalDensity (Real.pi * Real.exp (4*s)) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
              intro s hs
              exact (thetaOriginalDensity_at_exp s).symm
    _ = _ := theta_exp_change_variables thetaOriginalDensity t

end W5
