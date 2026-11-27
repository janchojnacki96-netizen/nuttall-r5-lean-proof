import Nuttall.ShiftCentralCircle
import Nuttall.ShiftCircleCoefficient
import Nuttall.ShiftAngularGaussian

namespace Nuttall

open Complex Polynomial MeasureTheory intervalIntegral
open scoped Polynomial Real

/-- The coefficient of the central product is bounded by the angular Gaussian
with the explicit (1/(cdsqrt M)) factor. -/
theorem norm_central_shift_polynomialCoeff_le {M j : ℕ} (hM : 0 < M) (hj : j ≤ M)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (hunit : c^2+d^2 = 1) (i : ℕ) :
    ‖(((C (c:ℂ)+C (d:ℂ)*X)^(M-j)) * (C (d:ℂ)-C (c:ℂ)*X)^j).coeff i‖ ≤
      Real.exp (4*((M:ℝ)/2-j)^2/M) * Real.sqrt π / (c*d*Real.sqrt M) := by
  let P : ℂ[X] := (C (c:ℂ)+C (d:ℂ)*X)^(M-j) * (C (d:ℂ)-C (c:ℂ)*X)^j
  let b : ℝ := (M:ℝ)*(c*d/2)^2
  let a : ℝ := Real.exp (4*((M:ℝ)/2-j)^2/M)
  let F (t : ℝ) := ‖P.eval (Complex.exp ((t:ℂ)*I))‖
  let G (t : ℝ) := Real.exp (-b*(Real.cos t)^2)
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hb : 0 < b := by dsimp [b]; positivity
  have ha : 0 ≤ a := Real.exp_nonneg _
  have hf : Continuous F := by
    unfold F
    exact (P.continuous.comp (by fun_prop)).norm
  have hg : Continuous G := by unfold G; fun_prop
  have hFG : ∀ t, F t ≤ a*G t := by
    intro t
    have h := shiftCentral_circle_product_bound hM hj hunit t
    dsimp [F, P, a, G, b] at *
    simp only [eval_mul, eval_pow, eval_add, eval_sub, eval_C, eval_X]
    rw [← Real.exp_add]
    convert h using 1
    congr 1
    ring
  have hInt := intervalIntegral.integral_mono_on (μ := (volume : Measure ℝ))
    (show (0:ℝ) ≤ 2*π by positivity) (hf.intervalIntegrable _ _)
    ((continuous_const.mul hg).intervalIntegrable _ _) (fun t _ => hFG t)
  change (∫ t in (0:ℝ)..2*π, F t) ≤ ∫ t in (0:ℝ)..2*π, a * G t at hInt
  rw [intervalIntegral.integral_const_mul] at hInt
  have hgauss := shiftAngularGaussian_average hb
  have hroot : Real.sqrt b = Real.sqrt (M:ℝ)*(c*d/2) := by
    dsimp [b]
    rw [Real.sqrt_mul hMr.le, Real.sqrt_sq (by positivity)]
  change ‖P.coeff i‖ ≤ a * Real.sqrt π / (c*d*Real.sqrt M)
  calc
    _ ≤ Real.circleAverage (fun z => ‖P.eval z‖) 0 1 := norm_polynomialCoeff_le_circleAverage P i
    _ = (1/(2*π)) * ∫ t in (0:ℝ)..2*π, F t := by
      simp only [Real.circleAverage_def, one_div, smul_eq_mul, circleMap_zero, ofReal_one, one_mul, F]
    _ ≤ (1/(2*π)) * (a * ∫ t in (0:ℝ)..2*π, G t) :=
      mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = a * ((1/(2*π)) * ∫ t in (0:ℝ)..2*π, G t) := by ring
    _ ≤ a * (Real.sqrt π / (2*Real.sqrt b)) := mul_le_mul_of_nonneg_left hgauss ha
    _ = _ := by
      rw [hroot, show 2*(Real.sqrt (M:ℝ)*(c*d/2)) = c*d*Real.sqrt M by ring, mul_div_assoc]

#print axioms norm_central_shift_polynomialCoeff_le

end Nuttall
