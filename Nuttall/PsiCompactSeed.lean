import Nuttall.FirstWronskian
import Nuttall.ThetaAuxiliaryIntegral
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Nuttall

open MeasureTheory Set

private theorem coordinate_at_two_ge : (4096:ℝ) ≤ Real.pi * Real.exp 8 := by
  have he : (5:ℝ)/2 ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/2) he 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have hh := mul_le_mul Real.pi_gt_three.le hp
    (by norm_num : (0:ℝ) ≤ 390625/256) Real.pi_pos.le
  linarith only [hh]

private theorem aux_two_succ_le (k : ℕ) :
    auxiliarySummand (k+1) 2 ≤ (18:ℝ) * (1/2:ℝ)^(2048+k) := by
  let x := ((k+1:ℕ):ℝ)^2 * Real.pi * Real.exp 8
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hs : (1:ℝ) + k ≤ ((k+1:ℕ):ℝ)^2 := by
    push_cast
    nlinarith only [sq_nonneg (k:ℝ), Nat.cast_nonneg (α := ℝ) k]
  have hx' : (4096:ℝ) * (1 + k) ≤ x := by
    dsimp [x]
    rw [mul_assoc, mul_comm 4096]
    exact mul_le_mul hs coordinate_at_two_ge (by positivity) (by positivity)
  have haux : auxiliarySummand (k+1) 2 = Real.exp 2 * x * Real.exp (-x) := by
    unfold auxiliarySummand x
    norm_num only
    rw [show (10:ℝ) = 2 + 8 by norm_num, Real.exp_add]
    ring
  have h₁ : x ≤ 2 * Real.exp (x/2) := by
    have h := Real.pow_div_factorial_le_exp (x/2) (by positivity) 1
    norm_num at h
    linarith only [h]
  have h₂ : Real.exp 2 ≤ 9 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith only [Real.exp_pos 1, Real.exp_one_lt_three,
      sq_nonneg (Real.exp 1 - 3)]
  have h₃ : Real.exp (-(x/2)) ≤ (1/2:ℝ)^(2048+k) := by
    have hn : -(x/2) ≤ (↑(2048+k):ℝ) * (-1) := by
      push_cast
      linarith only [hx', Nat.cast_nonneg (α := ℝ) k]
    have hb : Real.exp (-1) ≤ (1:ℝ)/2 := by
      rw [Real.exp_neg]
      simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ) < 2) Real.exp_one_gt_two.le
    calc
      _ ≤ Real.exp ((↑(2048+k):ℝ) * (-1)) := Real.exp_le_exp.mpr hn
      _ = Real.exp (-1)^(2048+k) := Real.exp_nat_mul _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hb _
  rw [haux]
  calc
    _ ≤ (9:ℝ) * (2 * Real.exp (x/2)) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul h₂ h₁ hx (by norm_num)) (Real.exp_pos _).le
    _ = 18 * Real.exp (-(x/2)) := by
      rw [show -(x/2) = x/2 + -x by ring, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h₃ (by norm_num)

set_option exponentiation.threshold 2400 in
/-- The analytic starting interval for backwards Taylor quadrature. -/
theorem psi_one_at_two_bounds : 0 ≤ psi 1 2 ∧ psi 1 2 ≤ (1/2:ℝ)^500 := by
  refine ⟨(psi_pos 1 2 (by norm_num)).le, ?_⟩
  have hg : Summable fun k : ℕ => (1/2:ℝ)^k :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have haux : auxiliaryTheta 2 ≤ (36:ℝ) * (1/2:ℝ)^2048 := by
    rw [auxiliaryTheta, ← (auxiliarySummand_summable 2).sum_add_tsum_nat_add 1]
    simp only [Finset.sum_range_one, auxiliarySummand, Nat.cast_zero,
      zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add]
    have hM : Summable fun k : ℕ => (18:ℝ) * (1/2:ℝ)^(2048+k) := by
      convert hg.mul_left ((18:ℝ) * (1/2:ℝ)^2048) using 1
      funext k
      rw [pow_add]
      ring
    have hS := (auxiliarySummand_summable 2).comp_injective
      (show Function.Injective (fun k : ℕ => k+1) from fun _ _ h => Nat.add_right_cancel h)
    change Summable (fun k : ℕ => auxiliarySummand (k+1) 2) at hS
    calc
      (∑' k, auxiliarySummand (k+1) 2) ≤ ∑' k : ℕ, (18:ℝ) * (1/2:ℝ)^(2048+k) :=
        hS.tsum_le_tsum aux_two_succ_le hM
      _ = _ := by
        simp only [pow_add, ← mul_assoc, tsum_mul_left]
        rw [tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖(1/2:ℝ)‖ < 1)]
        ring
  have hnonneg : 0 ≤ tailIntegral auxiliaryTheta 2 :=
    integral_nonneg (fun t => auxiliaryTheta_nonneg t)
  have h := twice_psi_one_eq_auxiliary_sub_tail 2 (by norm_num)
  have hsmall : (36:ℝ) * (1/2:ℝ)^2048 ≤ 2 * (1/2:ℝ)^500 := by norm_num
  linarith only [h, haux, hnonneg, hsmall]

#print axioms psi_one_at_two_bounds

end Nuttall
