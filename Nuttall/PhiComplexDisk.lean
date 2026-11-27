import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Nuttall

open Metric

/-- The complex extension of the square-index Gaussian coordinate. -/
noncomputable def phiComplexCoordinate (n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ)^2 * (Real.pi : ℂ) * Complex.exp (4*z)

/-- A holomorphic extension of the individual theta summand. -/
noncomputable def phiComplexSummand (n : ℕ) (z : ℂ) : ℂ :=
  let x := phiComplexCoordinate n z
  Complex.exp z * (2*x^2 - 3*x) * Complex.exp (-x)

private theorem exp_half_le : Real.exp (1/2) ≤ (7:ℝ)/4 := by
  have h := Real.exp_one_lt_three
  rw [show (1:ℝ) = 1/2 + 1/2 by norm_num, Real.exp_add] at h
  nlinarith only [h, Real.exp_pos (1/2), sq_nonneg (Real.exp (1/2) - 7/4)]

private theorem exp_seventeen_eighths_le : Real.exp (17/8) ≤ (9:ℝ) := by
  have h₁ : Real.exp 1 ≤ (11:ℝ)/4 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have h₂ : Real.exp (1/8) ≤ (8:ℝ)/7 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1:ℝ)/8) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [show (17:ℝ)/8 = 1+1+1/8 by norm_num, Real.exp_add, Real.exp_add 1 1]
  calc
    _ ≤ (((11:ℝ)/4) * ((11:ℝ)/4)) * ((8:ℝ)/7) := by
      apply mul_le_mul _ h₂ (Real.exp_pos _).le (by norm_num)
      exact mul_le_mul h₁ h₁ (Real.exp_pos _).le (by norm_num)
    _ ≤ _ := by norm_num

private theorem near_exp_bounds {w : ℂ} (hw : ‖w‖ ≤ 1/8) :
    ‖Complex.exp (4*w)‖ ≤ 2 ∧ (1:ℝ)/2 ≤ (Complex.exp (4*w)).re := by
  have hre := abs_le.mp ((Complex.abs_re_le_norm w).trans hw)
  have him := (Complex.abs_im_le_norm w).trans hw
  have hcos : (7:ℝ)/8 ≤ Real.cos (4*w.im) := by
    have habs : |4*w.im| ≤ 1/2 := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]; linarith only [him]
    have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hs
    linarith only [Real.one_sub_sq_div_two_le_cos (x := 4*w.im), hs]
  have hlo : (4:ℝ)/7 ≤ Real.exp (4*w.re) := by
    have hi := inv_anti₀ (Real.exp_pos (1/2)) exp_half_le
    rw [← Real.exp_neg] at hi
    exact (by simpa using hi : (4:ℝ)/7 ≤ Real.exp (-(1/2))).trans
      (Real.exp_le_exp.mpr (by linarith only [hre.1]))
  have hR : (4:ℂ).re = 4 := by norm_num
  have hI : (4:ℂ).im = 0 := by norm_num
  constructor
  · rw [Complex.norm_exp]
    simp only [Complex.mul_re, hR, hI, zero_mul, sub_zero]
    exact ((Real.exp_le_exp.mpr (by linarith only [hre.2])).trans exp_half_le).trans (by norm_num)
  · rw [Complex.exp_re]
    simp only [Complex.mul_re, Complex.mul_im, hR, hI, zero_mul, sub_zero, add_zero]
    calc
      (1:ℝ)/2 = (4:ℝ)/7 * ((7:ℝ)/8) := by norm_num
      _ ≤ _ := mul_le_mul hlo hcos (by norm_num) (Real.exp_pos _).le

/-- The disk estimate used for the rank-seven and rank-eight compact certificates. -/
theorem phiComplexSummand_norm_le_disk (n : ℕ) {c : ℝ} (hc : c ≤ 2)
    {z : ℂ} (hz : ‖z - (c : ℂ)‖ ≤ 1/8) :
    ‖phiComplexSummand n z‖ ≤
      20000 * Real.exp (-((n:ℝ)^2 * Real.pi * Real.exp (4*c))/3) := by
  let y := (n:ℝ)^2 * Real.pi * Real.exp (4*c)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  obtain ⟨hn, hr⟩ := near_exp_bounds hz
  have hx : phiComplexCoordinate n z = (y : ℂ) * Complex.exp (4*(z-(c:ℂ))) := by
    unfold phiComplexCoordinate y
    push_cast
    rw [mul_assoc ((n:ℂ)^2 * (Real.pi:ℂ)), ← Complex.exp_add]
    congr 2
    ring
  have hxnorm : ‖phiComplexCoordinate n z‖ ≤ 2*y := by
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy, mul_comm 2 y]
    exact mul_le_mul_of_nonneg_left hn hy
  have hxre : y/2 ≤ (phiComplexCoordinate n z).re := by
    rw [hx, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      y/2 = y*(1/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr hy
  have hEz : ‖Complex.exp z‖ ≤ 9 := by
    have hp := (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
    simp only [Complex.sub_re, Complex.ofReal_re] at hp
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr (by linarith only [(abs_le.mp hp).2, hc])).trans exp_seventeen_eighths_le
  have hp : ‖2 * phiComplexCoordinate n z ^ 2 - 3 * phiComplexCoordinate n z‖ ≤
      8*y^2 + 6*y := by
    refine norm_sub_le _ _ |>.trans ?_
    simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hxnorm 2
    nlinarith only [hsq, hxnorm]
  have he : ‖Complex.exp (-phiComplexCoordinate n z)‖ ≤ Real.exp (-y/2) := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (by linarith only [hxre])
  have h₁ : y ≤ 6 * Real.exp (y/6) := by
    have h := Real.pow_div_factorial_le_exp (y/6) (by positivity) 1
    norm_num at h
    linarith only [h]
  have h₂ : y^2 ≤ 72 * Real.exp (y/6) := by
    have h := Real.pow_div_factorial_le_exp (y/6) (by positivity) 2
    norm_num [div_pow, Nat.factorial] at h
    linarith only [h]
  unfold phiComplexSummand
  simp only [norm_mul]
  calc
    _ ≤ 9 * (8*y^2 + 6*y) * Real.exp (-y/2) :=
      mul_le_mul (mul_le_mul hEz hp (norm_nonneg _) (by norm_num)) he
        (norm_nonneg _) (by positivity)
    _ ≤ 20000 * Real.exp (-y/3) := by
      have hP : 9 * (8*y^2 + 6*y) ≤ 20000 * Real.exp (y/6) := by
        nlinarith only [h₁, h₂, Real.exp_pos (y/6)]
      calc
        _ ≤ 20000 * Real.exp (y/6) * Real.exp (-y/2) :=
          mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Cauchy bounds the complex derivative of an individual term at a real center. -/
theorem phiComplexSummand_iteratedDeriv_norm_le (n k : ℕ) {c : ℝ} (hc : c ≤ 2) :
    ‖iteratedDeriv k (phiComplexSummand n) (c : ℂ)‖ ≤
      (k.factorial : ℝ) * (20000 * Real.exp (-((n:ℝ)^2 * Real.pi * Real.exp (4*c))/3)) /
        (1/8 : ℝ)^k := by
  have hd : Differentiable ℂ (phiComplexSummand n) := by
    unfold phiComplexSummand phiComplexCoordinate
    fun_prop
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num)
    hd.diffContOnCl (fun z hz => phiComplexSummand_norm_le_disk n hc
      (mem_sphere_iff_norm.mp hz).le)

#print axioms phiComplexSummand_iteratedDeriv_norm_le

end Nuttall
