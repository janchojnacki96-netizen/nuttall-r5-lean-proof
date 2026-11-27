import Nuttall.PsiCompactSeed

namespace Nuttall

open MeasureTheory
open scoped BigOperators

private theorem seedSummand_le (t : ℝ) (hEt : Real.exp t ≤ 3) (b : ℕ) (hb : 1 ≤ b)
    (hX : (10:ℝ)/9 * b ≤ Real.pi * Real.exp (4*t)) (k : ℕ) :
    auxiliarySummand (k+1) t ≤ 30 * (3/8:ℝ)^(b+k) := by
  let n : ℝ := ((k+1:ℕ):ℝ)
  let x := n^2 * Real.pi * Real.exp (4*t)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx' : (10:ℝ)/9 * b * n^2 ≤ x := by
    unfold x
    calc
      _ = n^2 * ((10:ℝ)/9 * b) := by ring
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hX (sq_nonneg _)
  have haux : auxiliarySummand (k+1) t = Real.exp t * x * Real.exp (-x) := by
    unfold auxiliarySummand x n
    rw [show (5:ℝ)*t = t + 4*t by ring, Real.exp_add]
    ring
  have h₁ : x ≤ 10 * Real.exp (x/10) := by
    have h := Real.pow_div_factorial_le_exp (x/10) (by positivity) 1
    norm_num at h
    linarith only [h]
  have hq : Real.exp (-1) ≤ (3:ℝ)/8 := by
    have hh : (8:ℝ)/3 ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
    have hi := inv_anti₀ (by norm_num : (0:ℝ) < 8/3) hh
    rw [← Real.exp_neg] at hi
    norm_num at hi ⊢
    exact hi
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hnk : (b:ℝ) + k ≤ (b:ℝ) * n^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hbR hk
    have h₂ := mul_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans hbR) (sq_nonneg (k:ℝ))
    dsimp [n]
    push_cast
    nlinarith only [h₁, h₂, hk]
  have hpow : Real.exp (-(9*x/10)) ≤ (3/8:ℝ)^(b+k) := by
    calc
      _ ≤ Real.exp ((↑(b+k):ℝ)*(-1)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        linarith only [hx', hnk]
      _ = Real.exp (-1)^(b+k) := Real.exp_nat_mul _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hq _
  rw [haux]
  calc
    _ ≤ (3:ℝ) * (10 * Real.exp (x/10)) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hEt h₁ hx (by norm_num)) (Real.exp_pos _).le
    _ = 30 * Real.exp (-(9*x/10)) := by
      rw [show -(9*x/10) = x/10 + -x by ring, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)

private theorem seed_auxiliaryTheta_le (t : ℝ) (hEt : Real.exp t ≤ 3)
    (b : ℕ) (hb : 1 ≤ b) (hX : (10:ℝ)/9 * b ≤ Real.pi * Real.exp (4*t)) :
    auxiliaryTheta t ≤ (30:ℝ) * (3/8:ℝ)^b / (1-3/8) := by
  have hg : Summable fun k : ℕ => (3/8:ℝ)^k :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have hM : Summable fun k : ℕ => (30:ℝ) * (3/8:ℝ)^(b+k) := by
    convert hg.mul_left (30 * (3/8:ℝ)^b) using 1
    funext k
    rw [pow_add]
    ring
  have hS := (auxiliarySummand_summable t).comp_injective
    (show Function.Injective (fun k : ℕ => k+1) from fun _ _ h => Nat.add_right_cancel h)
  change Summable (fun k : ℕ => auxiliarySummand (k+1) t) at hS
  rw [auxiliaryTheta, ← (auxiliarySummand_summable t).sum_add_tsum_nat_add 1]
  have hzero : auxiliarySummand 0 t = 0 := by simp [auxiliarySummand]
  rw [Finset.sum_range_one, hzero, zero_add]
  refine (hS.tsum_le_tsum (seedSummand_le t hEt b hb hX) hM).trans_eq ?_
  simp only [pow_add, ← mul_assoc, tsum_mul_left]
  rw [tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖(3/8:ℝ)‖ < 1)]
  ring

/-- A stronger starting enclosure for the late rank-seven cells. -/
theorem psi_one_precise_compact_seed_bounds {t : ℝ}
    (ht : (11:ℝ)/16 ≤ t) (ht₁ : t ≤ 1) :
    0 ≤ psi 1 t ∧ psi 1 t ≤ 1/10^16 := by
  have ht₀ : 0 ≤ t := (by norm_num : (0:ℝ) ≤ 11/16).trans ht
  refine ⟨(psi_pos 1 t ht₀).le, ?_⟩
  have hEt := (Real.exp_le_exp.mpr ht₁).trans Real.exp_one_lt_three.le
  have hX : (10:ℝ)/9 * 43 ≤ Real.pi * Real.exp (4*t) := by
    have he := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 11/4 by norm_num) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at he
    have he₁ : (153:ℝ)/10 ≤ Real.exp (11/4) := by linarith only [he]
    have he₂ := he₁.trans (Real.exp_le_exp.mpr (show (11:ℝ)/4 ≤ 4*t by linarith only [ht]))
    have hπ : (314:ℝ)/100 ≤ Real.pi := Real.pi_gt_d6.le.trans' (by norm_num)
    have h := mul_le_mul hπ he₂ (by norm_num) Real.pi_pos.le
    linarith only [h]
  have haux := seed_auxiliaryTheta_le t hEt 43 (by decide) (by
    norm_num at hX ⊢
    exact hX)
  have hsmall : (30:ℝ) * (3/8:ℝ)^43 / (1-3/8) ≤ 2/10^16 := by norm_num
  have hnonneg : 0 ≤ tailIntegral auxiliaryTheta t :=
    integral_nonneg (fun u => auxiliaryTheta_nonneg u)
  linarith only [twice_psi_one_eq_auxiliary_sub_tail t ht₀, haux, hsmall, hnonneg]

#print axioms psi_one_precise_compact_seed_bounds

end Nuttall
