import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Scale the theta incomplete-gamma tail to the fixed interval (1,infinity)

A genuine half-line change-of-variables theorem:
  int_a^infinity y^(1/4) exp(-p*y) dy
  = a^(5/4) * int_1^infinity v^(1/4) exp(-p*a*v) dv, a>0.

This is exactly the final rescaling needed to recover the
bracketed single-square term of the theta certificate.
-/

namespace W5

open MeasureTheory

theorem theta_quarter_integral_scale (p a : ℝ) (ha : 0 < a) :
    (∫ y in Set.Ioi a,
       y ^ ((1:ℝ)/4) * Real.exp (-p*y)) =
      a ^ ((5:ℝ)/4) *
        (∫ v in Set.Ioi (1:ℝ),
          v ^ ((1:ℝ)/4) * Real.exp (-p*a*v)) := by
  let g : ℝ → ℝ :=
    fun y => y ^ ((1:ℝ)/4) * Real.exp (-p*y)
  have hsubst :
      (∫ v in Set.Ioi (1:ℝ), g (a*v)) =
        a⁻¹ * (∫ y in Set.Ioi a, g y) := by
    simpa only [mul_one, smul_eq_mul] using
      (MeasureTheory.integral_comp_mul_left_Ioi g 1 ha)
  have hcongr :
      (∫ v in Set.Ioi (1:ℝ), g (a*v)) =
        (∫ v in Set.Ioi (1:ℝ),
          a ^ ((1:ℝ)/4) *
            (v ^ ((1:ℝ)/4) * Real.exp (-p*a*v))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hv0 : 0 ≤ v :=
      le_of_lt (lt_trans (by norm_num : (0:ℝ) < 1) hv)
    dsimp only [g]
    rw [Real.mul_rpow (le_of_lt ha) hv0]
    have he : -p*(a*v) = -p*a*v := by ring
    rw [he]
    ring
  have hfactor :
      (∫ v in Set.Ioi (1:ℝ), g (a*v)) =
        a ^ ((1:ℝ)/4) *
          (∫ v in Set.Ioi (1:ℝ),
            v ^ ((1:ℝ)/4) * Real.exp (-p*a*v)) := by
    rw [hcongr, integral_const_mul]
  have hpower : a ^ ((5:ℝ)/4) = a*a ^ ((1:ℝ)/4) := by
    have he : ((5:ℝ)/4) = 1 + ((1:ℝ)/4) := by ring
    rw [he, Real.rpow_add ha, Real.rpow_one]
  have hr :
      (∫ y in Set.Ioi a, g y) =
        a ^ ((5:ℝ)/4) *
          (∫ v in Set.Ioi (1:ℝ),
            v ^ ((1:ℝ)/4) * Real.exp (-p*a*v)) := by
    calc
      (∫ y in Set.Ioi a, g y) =
          a*(a⁻¹*(∫ y in Set.Ioi a, g y)) := by
            field_simp [ne_of_gt ha]
      _ = a*(∫ v in Set.Ioi (1:ℝ), g (a*v)) := by
            rw [hsubst]
      _ = a*(a ^ ((1:ℝ)/4) *
          (∫ v in Set.Ioi (1:ℝ),
            v ^ ((1:ℝ)/4) * Real.exp (-p*a*v))) := by
            rw [hfactor]
      _ = a ^ ((5:ℝ)/4) *
          (∫ v in Set.Ioi (1:ℝ),
            v ^ ((1:ℝ)/4) * Real.exp (-p*a*v)) := by
            rw [hpower]
            ring
  simpa only [g] using hr

end W5
