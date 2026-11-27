import Nuttall.PhiJetCoefficients

namespace Nuttall

open scoped BigOperators

private theorem phiJetCoeff_abs_sum_le {j : ℕ} (hj : j ≤ 8) :
    (∑ k ∈ Finset.range 10, |phiJetCoeff j k|) ≤ (10 : ℚ)^11 := by
  interval_cases j <;> decide +kernel

private theorem phiJetPolynomial_abs_le {j : ℕ} (hj : j ≤ 8) {x : ℝ} (hx : 1 ≤ x) :
    |(phiJetPolynomial j).eval x| ≤ (10 : ℝ)^11 * x^9 := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hc : (∑ k ∈ Finset.range 10, |(phiJetCoeff j k : ℝ)|) ≤ (10 : ℝ)^11 := by
    exact_mod_cast phiJetCoeff_abs_sum_le hj
  rw [eval_phiJetPolynomial hj]
  calc
    _ ≤ ∑ k ∈ Finset.range 10, |(phiJetCoeff j k : ℝ) * x^k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range 10, |(phiJetCoeff j k : ℝ)| * x^9 := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx₀ _)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hx (by have := Finset.mem_range.mp hk; omega)) (abs_nonneg _)
    _ = (∑ k ∈ Finset.range 10, |(phiJetCoeff j k : ℝ)|) * x^9 := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (pow_nonneg hx₀ _)

private theorem exp_neg_three_halves_le :
    Real.exp (-(3/2 : ℝ)) ≤ 1/4 := by
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 3/2 by norm_num) 4
  have h₄ : (4:ℝ) ≤ Real.exp (3/2) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  rw [Real.exp_neg]
  simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ) < 4) h₄

private theorem phiOriginSummand_abs_le {j : ℕ} (hj : j ≤ 8) (k : ℕ) :
    |auxiliaryWeightedSummand (phiJetPolynomial j) (k + 8) 0| ≤
      (10:ℝ)^24 * (1/4 : ℝ)^(64 + k) := by
  let n := k + 8
  let x := (n : ℝ)^2 * Real.pi
  have hn : (8 : ℝ) ≤ n := by dsimp [n]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) k]
  have hxL : 3 * (n:ℝ)^2 ≤ x := by
    dsimp [x]
    calc
      _ = (n:ℝ)^2 * 3 := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left Real.pi_gt_three.le (sq_nonneg (n:ℝ))
  have hx : 1 ≤ x := by nlinarith only [sq_nonneg ((n:ℝ) - 8), hn, hxL]
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hA : auxiliaryWeightedSummand (phiJetPolynomial j) n 0 =
      x * (phiJetPolynomial j).eval x * Real.exp (-x) := by
    rw [auxiliaryWeightedSummand_origin, ← Real.exp_nat_mul, Nat.cast_pow]
    congr 2
    dsimp [x]
    ring
  have hP : x^10 ≤ ((2 : ℝ)^10 * (Nat.factorial 10 : ℝ)) * Real.exp (x/2) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (Nat.factorial 10 : ℝ))).1
      (Real.pow_div_factorial_le_exp (x/2) (by positivity) 10)
    rw [div_pow] at h
    calc
      _ = (2:ℝ)^10 * (x^10 / (2:ℝ)^10) := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 2^10)
        simpa only [mul_assoc, mul_comm (Real.exp (x/2))] using hh
  have hxG : -(x/2) ≤ (64 + (k:ℝ)) * (-(3/2 : ℝ)) := by
    dsimp [n] at hxL
    push_cast at hxL
    nlinarith only [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k, hxL]
  change |auxiliaryWeightedSummand (phiJetPolynomial j) n 0| ≤ _
  rw [hA, abs_mul, abs_mul, abs_of_nonneg hx₀, abs_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ x * ((10:ℝ)^11 * x^9) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (phiJetPolynomial_abs_le hj hx) hx₀) (Real.exp_pos _).le
    _ = (10:ℝ)^11 * x^10 * Real.exp (-x) := by ring
    _ ≤ (10:ℝ)^11 * (((2:ℝ)^10 * (Nat.factorial 10:ℝ)) * Real.exp (x/2)) *
        Real.exp (-x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by positivity))
        (Real.exp_pos _).le
    _ = ((10:ℝ)^11 * ((2:ℝ)^10 * (Nat.factorial 10:ℝ))) * Real.exp (-(x/2)) := by
      rw [show -(x/2) = x/2 + -x by ring, Real.exp_add]
      ring
    _ ≤ (10:ℝ)^24 * Real.exp (-(x/2)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      norm_num [Nat.factorial]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ Real.exp ((↑(64+k) : ℝ) * (-(3/2 : ℝ))) := Real.exp_le_exp.mpr (by push_cast; exact hxG)
        _ = Real.exp (-(3/2 : ℝ))^(64+k) := Real.exp_nat_mul _ _
        _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_three_halves_le _

/-- A common bound on all nine tails after the index-seven term. -/
theorem phiOriginTail_abs_le {j : ℕ} (hj : j ≤ 8) :
    |∑' k, auxiliaryWeightedSummand (phiJetPolynomial j) (k+8) 0| ≤ (1:ℝ)/10^12 := by
  have hg : Summable (fun k : ℕ => (1/4:ℝ)^k) :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have hG : Summable (fun k : ℕ => (10:ℝ)^24 * (1/4:ℝ)^(64+k)) := by
    simpa only [pow_add, mul_assoc] using ((hg.mul_left ((1/4:ℝ)^64)).mul_left ((10:ℝ)^24))
  have hN : Summable (fun k : ℕ => ‖auxiliaryWeightedSummand (phiJetPolynomial j) (k+8) 0‖) :=
    hG.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      simpa only [Real.norm_eq_abs] using phiOriginSummand_abs_le hj k)
  calc
    _ ≤ ∑' k, ‖auxiliaryWeightedSummand (phiJetPolynomial j) (k+8) 0‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hN
    _ ≤ ∑' k : ℕ, (10:ℝ)^24 * (1/4:ℝ)^(64+k) :=
      hN.tsum_le_tsum (fun k => by simpa only [Real.norm_eq_abs] using phiOriginSummand_abs_le hj k) hG
    _ ≤ _ := by
      simp only [pow_add, ← mul_assoc, tsum_mul_left]
      rw [tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖(1/4:ℝ)‖ < 1)]
      norm_num

#print axioms phiOriginTail_abs_le

end Nuttall
