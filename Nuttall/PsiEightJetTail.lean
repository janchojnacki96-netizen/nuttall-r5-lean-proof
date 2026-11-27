import Nuttall.PhiJetCoefficients
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Nuttall

open scoped BigOperators

set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
private theorem rankEight_coeff_bound {j : ℕ} (hj : j ≤ 13) :
    (∑ k ∈ Finset.range 15, |phiJetCoeff j k| * (2^(k+1) * ((k+1).factorial : ℚ))) ≤
      (10 : ℚ)^27 := by
  interval_cases j <;> decide +kernel

private theorem exp_neg_two_le_quarter : Real.exp (-2) ≤ (1:ℝ)/4 := by
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2 by norm_num) 3
  have h₄ : (4:ℝ) ≤ Real.exp 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  rw [Real.exp_neg]
  simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ) < 4) h₄

set_option maxHeartbeats 2000000 in
/-- The nine-term truncation has a common rational remainder for the witness jets. -/
theorem rankEight_phiJetTail_abs_le {j : ℕ} (hj : j ≤ 13) {t : ℝ}
    (ht : t ≤ 1) (hX : 4 ≤ Real.pi * Real.exp (4*t)) :
    |∑' k, auxiliaryWeightedSummand (phiJetPolynomial j) (k+9) t| ≤ (1:ℝ)/10^12 := by
  have hC : (∑ k ∈ Finset.range 15, |(phiJetPolynomial j).coeff k| *
      (2^(k+1) * ((k+1).factorial : ℝ))) ≤ (10:ℝ)^27 := by
    simp only [coeff_phiJetPolynomial]
    exact_mod_cast rankEight_coeff_bound hj
  have hterm (k : ℕ) : ‖auxiliaryWeightedSummand (phiJetPolynomial j) (k+9) t‖ ≤
      (3 * 10^27:ℝ) * (1/4:ℝ)^(81+k) := by
    have hcoord : 4 * ((k:ℝ)+9)^2 ≤ auxiliaryCoordinate (k+9) t := by
      unfold auxiliaryCoordinate
      push_cast
      rw [mul_comm 4, mul_assoc]
      exact mul_le_mul_of_nonneg_left hX (sq_nonneg _)
    have hexp : -auxiliaryCoordinate (k+9) t / 2 ≤ (↑(81+k) : ℝ) * (-2) := by
      push_cast
      nlinarith only [hcoord, sq_nonneg (k:ℝ), Nat.cast_nonneg (α := ℝ) k]
    have hsmall : Real.exp (-auxiliaryCoordinate (k+9) t / 2) ≤ (1/4:ℝ)^(81+k) := by
      calc
        _ ≤ Real.exp ((↑(81+k):ℝ) * (-2)) := Real.exp_le_exp.mpr hexp
        _ = Real.exp (-2)^(81+k) := Real.exp_nat_mul _ _
        _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_two_le_quarter _
    have hEt : Real.exp t ≤ 3 := (Real.exp_le_exp.mpr ht).trans Real.exp_one_lt_three.le
    calc
      _ ≤ (10:ℝ)^27 * Real.exp (t - auxiliaryCoordinate (k+9) t / 2) :=
        auxiliaryWeightedSummand_le_exp_of_coeff_bound _ _ _ _ _
          ((phiJetPolynomial_natDegree_le j).trans_lt (by omega)) hC
      _ = (10:ℝ)^27 * (Real.exp t * Real.exp (-auxiliaryCoordinate (k+9) t / 2)) := by
        rw [show t - auxiliaryCoordinate (k+9) t / 2 =
          t + -auxiliaryCoordinate (k+9) t / 2 by ring, Real.exp_add]
      _ ≤ (10:ℝ)^27 * (3 * (1/4:ℝ)^(81+k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hEt hsmall (Real.exp_pos _).le (by norm_num)) (by positivity)
      _ = _ := by ring
  have hg : Summable (fun k : ℕ => (1/4:ℝ)^k) :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have hG : Summable (fun k : ℕ => (3 * 10^27:ℝ) * (1/4:ℝ)^(81+k)) := by
    convert hg.mul_left ((3 * 10^27:ℝ) * (1/4:ℝ)^81) using 1
    funext k
    rw [pow_add]
    ring
  have hN : Summable (fun k : ℕ => ‖auxiliaryWeightedSummand (phiJetPolynomial j) (k+9) t‖) :=
    hG.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc
    _ ≤ ∑' k, ‖auxiliaryWeightedSummand (phiJetPolynomial j) (k+9) t‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hN
    _ ≤ ∑' k : ℕ, (3 * 10^27:ℝ) * (1/4:ℝ)^(81+k) :=
      hN.tsum_le_tsum hterm hG
    _ ≤ _ := by
      simp only [pow_add, ← mul_assoc, tsum_mul_left]
      rw [tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖(1/4:ℝ)‖ < 1)]
      norm_num

#print axioms rankEight_phiJetTail_abs_le

end Nuttall
