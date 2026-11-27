import Nuttall.PsiOneTailBound
import Nuttall.PhiCompactExponential

namespace Nuttall

open scoped BigOperators

private theorem lower_exp_neg_rankEight_coordinate :
    (0.01363:ℝ) ≤ Real.exp (-(Real.pi * Real.exp (4*((5:ℝ)/64)))) := by
  have hlo := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/16 by norm_num) 8
  have hhi := Real.exp_bound' (n := 8) (show (0:ℝ) ≤ 5/16 by norm_num)
    (show (5:ℝ)/16 ≤ 1 by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo hhi
  have hl : (1.36683793:ℝ) ≤ Real.exp (5/16) := by linarith only [hlo]
  have hh : Real.exp (5/16) ≤ (1.36683795:ℝ) := by linarith only [hhi]
  have hp := mul_le_mul Real.pi_gt_d6.le hl (by norm_num : (0:ℝ) ≤ 1.36683793) Real.pi_pos.le
  have hq := mul_le_mul Real.pi_lt_d6.le hh (Real.exp_pos _).le
    (by norm_num : (0:ℝ) ≤ 3.141593)
  have he : (4:ℝ)*((5:ℝ)/64) = 5/16 := by norm_num
  have hA : ((4294/1000:ℚ):ℝ) ≤ Real.pi * Real.exp (4*((5:ℝ)/64)) := by
    rw [he]
    norm_num at hp ⊢
    linarith only [hp]
  have hB : Real.pi * Real.exp (4*((5:ℝ)/64)) ≤ ((4295/1000:ℚ):ℝ) := by
    rw [he]
    norm_num at hq ⊢
    linarith only [hq]
  have h := (phiCompactExpBox_containsReal (by norm_num) (by norm_num) hA hB).1
  have hb : (1363/100000:ℚ) ≤ (phiCompactExpBox (4294/1000) (4295/1000)).lo := by
    decide +kernel
  have hLower : ((1363/100000:ℚ):ℝ) ≤
      ((phiCompactExpBox (4294/1000) (4295/1000)).lo : ℝ) := Rat.cast_mono hb
  have heq : ((1363/100000:ℚ):ℝ) = (0.01363:ℝ) := by norm_num
  rw [heq] at hLower
  exact hLower.trans h

/-- A rational lower bound for the corner entry at the rank-eight witness. -/
theorem psi_one_at_rankEight_witness_ge :
    (29:ℝ)/1000 ≤ psi 1 (5/64) := by
  let t : ℝ := 5/64
  have ht : 0 ≤ t := by norm_num [t]
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ 5*t by positivity) 5
  norm_num [t, Finset.sum_range_succ, Nat.factorial] at he
  have he5 : (1.47782:ℝ) ≤ Real.exp (5*t) := by
    dsimp [t]
    norm_num
    linarith only [he]
  have hterm := (auxiliarySummand_summable t).le_tsum 1
    (fun n _ => by unfold auxiliarySummand; positivity)
  have h1 : auxiliarySummand 1 t ≤ auxiliaryTheta t := hterm
  have h2 : (3.141592:ℝ)*1.47782*0.01363 ≤ auxiliarySummand 1 t := by
    unfold auxiliarySummand
    simp only [Nat.cast_one, one_pow, one_mul]
    exact mul_le_mul
      (mul_le_mul Real.pi_gt_d6.le he5 (by norm_num) Real.pi_pos.le)
      (by simpa only [t, neg_one_mul, neg_mul, one_mul] using lower_exp_neg_rankEight_coordinate)
      (by norm_num) (by positivity)
  have he4 : (1.3668:ℝ) ≤ Real.exp (4*t) := by
    have h := Real.sum_le_exp_of_nonneg (show 0 ≤ 4*t by positivity) 5
    norm_num [t, Finset.sum_range_succ, Nat.factorial] at h
    dsimp [t]
    norm_num
    linarith only [h]
  have hc : (12:ℝ) ≤ 4 * (Real.pi * Real.exp (4*t)) - 5 := by
    have h := mul_le_mul Real.pi_gt_d6.le he4 (by norm_num) Real.pi_pos.le
    norm_num [t] at h ⊢
    linarith only [h]
  have hPsi := psi_one_ge_auxiliary_mul_rate t 12 ht (by norm_num) hc
  have hg := h2.trans h1
  norm_num at hg
  change (29:ℝ)/1000 ≤ psi 1 t
  linarith only [hPsi, hg]

#print axioms psi_one_at_rankEight_witness_ge

end Nuttall
