import Nuttall.PsiCompactSeed
import Nuttall.PsiDerivatives

namespace Nuttall

open MeasureTheory Set

private theorem mul_exp_neg_le_of_one_le {b x : ℝ} (hb : 1 ≤ b) (hx : b ≤ x) :
    x * Real.exp (-x) ≤ b * Real.exp (-b) := by
  let d := x-b
  have hd : 0 ≤ d := sub_nonneg.mpr hx
  have h₁ : x ≤ b * (1+d) := by
    have h := mul_le_mul_of_nonneg_right hb hd
    dsimp [d] at h ⊢
    nlinarith only [h]
  have h₂ : b * (1+d) ≤ b * Real.exp d :=
    mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp d)
      (by linarith only [hb])
  calc
    _ ≤ b * Real.exp d * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right (h₁.trans h₂) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add, show d + -x = -b by dsimp [d]; ring]

private theorem auxiliarySummand_half_le (k : ℕ) :
    auxiliarySummand (k+1) (1/2) ≤ 44 * (3/8:ℝ)^(21+k) := by
  let n : ℝ := ((k+1:ℕ):ℝ)
  let x := n^2 * Real.pi * Real.exp 2
  have hn : (1:ℝ) ≤ n^2 := by
    dsimp [n]
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) k, sq_nonneg (k:ℝ)]
  have hX : (22:ℝ) ≤ Real.pi * Real.exp 2 := by
    have he : (27:ℝ)/10 ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
    have he₂ := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) he 2
    rw [← Real.exp_nat_mul] at he₂
    norm_num at he₂
    have hπ : (31:ℝ)/10 ≤ Real.pi := Real.pi_gt_d6.le.trans' (by norm_num)
    have h := mul_le_mul hπ he₂ (by norm_num) Real.pi_pos.le
    linarith only [h]
  have hx : 22*n^2 ≤ x := by
    dsimp [x]
    rw [mul_assoc, mul_comm 22]
    exact mul_le_mul_of_nonneg_left hX (sq_nonneg _)
  have he : Real.exp (1/2) ≤ 2 := by
    have h := Real.exp_one_lt_three
    rw [show (1:ℝ) = 1/2+1/2 by norm_num, Real.exp_add] at h
    nlinarith only [h, Real.exp_pos (1/2), sq_nonneg (Real.exp (1/2)-2)]
  have ha : auxiliarySummand (k+1) (1/2) = Real.exp (1/2) * (x*Real.exp (-x)) := by
    unfold auxiliarySummand x n
    norm_num only
    rw [show (5:ℝ)/2 = 1/2+2 by norm_num, Real.exp_add]
    ring
  have hq : Real.exp (-1) ≤ (3:ℝ)/8 := by
    have hh : (8:ℝ)/3 ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
    have hi := inv_anti₀ (by norm_num : (0:ℝ) < 8/3) hh
    rw [← Real.exp_neg] at hi
    norm_num at hi ⊢
    exact hi
  have hpow : Real.exp (-(21*n^2)) ≤ (3/8:ℝ)^(21+k) := by
    calc
      _ ≤ Real.exp ((↑(21+k):ℝ)*(-1)) := by
        apply Real.exp_le_exp.mpr
        dsimp [n]
        push_cast
        nlinarith only [sq_nonneg (k:ℝ), Nat.cast_nonneg (α := ℝ) k]
      _ = Real.exp (-1)^(21+k) := Real.exp_nat_mul _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hq _
  have hnexp : n^2 ≤ Real.exp (n^2) := by linarith only [Real.add_one_le_exp (n^2)]
  have hmul := mul_exp_neg_le_of_one_le (show 1 ≤ 22*n^2 by linarith only [hn]) hx
  rw [ha]
  calc
    _ ≤ 2 * ((22*n^2) * Real.exp (-(22*n^2))) :=
      mul_le_mul he hmul (by positivity) (by norm_num)
    _ ≤ 2 * (22 * Real.exp (n^2) * Real.exp (-(22*n^2))) := by gcongr
    _ = 44 * Real.exp (-(21*n^2)) := by
      rw [mul_assoc 22, ← Real.exp_add, show n^2 + -(22*n^2) = -(21*n^2) by ring]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)

/-- A shorter quadrature seed suffices for the first rank-seven cell.
It reduces the candidate grid from 64 to 16 panels of width 1/32. -/
theorem psi_one_at_half_bounds : 0 ≤ psi 1 (1/2) ∧ psi 1 (1/2) ≤ 1/10^7 := by
  refine ⟨(psi_pos 1 _ (by norm_num)).le, ?_⟩
  have hg : Summable fun k : ℕ => (3/8:ℝ)^k :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have hM : Summable fun k : ℕ => (44:ℝ) * (3/8:ℝ)^(21+k) := by
    convert hg.mul_left (44 * (3/8:ℝ)^21) using 1
    funext k
    rw [pow_add]
    ring
  have hS := (auxiliarySummand_summable (1/2)).comp_injective
    (show Function.Injective (fun k : ℕ => k+1) from fun _ _ h => Nat.add_right_cancel h)
  change Summable (fun k : ℕ => auxiliarySummand (k+1) (1/2)) at hS
  have haux : auxiliaryTheta (1/2) ≤ 2/10^7 := by
    rw [auxiliaryTheta, ← (auxiliarySummand_summable (1/2)).sum_add_tsum_nat_add 1]
    have hzero : auxiliarySummand 0 (1/2) = 0 := by simp [auxiliarySummand]
    rw [Finset.sum_range_one, hzero, zero_add]
    refine (hS.tsum_le_tsum auxiliarySummand_half_le hM).trans ?_
    simp only [pow_add, ← mul_assoc, tsum_mul_left]
    rw [tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖(3/8:ℝ)‖ < 1)]
    norm_num
  have hnonneg : 0 ≤ tailIntegral auxiliaryTheta (1/2) :=
    integral_nonneg (fun t => auxiliaryTheta_nonneg t)
  have h := twice_psi_one_eq_auxiliary_sub_tail (1/2) (by norm_num)
  linarith only [h, haux, hnonneg]

/-- The shortened seed also applies when the uniform grid starts at a
positive center rather than at the origin. -/
theorem psi_one_short_seed_bounds {t : ℝ} (ht : (1:ℝ)/2 ≤ t) :
    0 ≤ psi 1 t ∧ psi 1 t ≤ 1/10^7 := by
  have hd (s : ℝ) : HasDerivAt (psi 1) (-W5.Phi s) s := psi_succ_hasDerivAt 0 s
  have hdiff : Differentiable ℝ (psi 1) := fun s => (hd s).differentiableAt
  have hanti : AntitoneOn (psi 1) (Ici (0:ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hdiff.continuous.continuousOn hdiff.differentiableOn
    intro s hs
    rw [(hd s).deriv]
    exact neg_nonpos.mpr (W5.Phi_pos s (mem_Ici.mp (interior_subset hs))).le
  have ht₀ : 0 ≤ t := (by norm_num : (0:ℝ) ≤ 1/2).trans ht
  exact ⟨(psi_pos 1 t ht₀).le,
    (hanti (by norm_num) (mem_Ici.mpr ht₀) ht).trans psi_one_at_half_bounds.2⟩

#print axioms psi_one_short_seed_bounds

end Nuttall
