import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

namespace Nuttall

private theorem exp_pi_quarter_bounds :
    (2.1932800507380 : ℝ) ≤ Real.exp (Real.pi/4) ∧
      Real.exp (Real.pi/4) ≤ 2.1932800507381 := by
  let a : ℝ := 3141592653589793 / 4000000000000000
  let b : ℝ := 3141592653589794 / 4000000000000000
  have ha : a ≤ Real.pi/4 := by dsimp [a]; linarith [Real.pi_gt_d20]
  have hb : Real.pi/4 ≤ b := by dsimp [b]; linarith [Real.pi_lt_d20]
  have h₁ := Real.sum_le_exp_of_nonneg (show 0 ≤ a by norm_num [a]) 17
  have h₂ := Real.exp_bound' (n := 17) (show 0 ≤ b by norm_num [b])
    (show b ≤ 1 by norm_num [b]) (by decide)
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ ∑ i ∈ Finset.range 17, a^i / (i.factorial : ℝ) := by
        norm_num [a, Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp a := h₁
      _ ≤ _ := Real.exp_le_exp.mpr ha
  · calc
      _ ≤ Real.exp b := Real.exp_le_exp.mpr hb
      _ ≤ (∑ i ∈ Finset.range 17, b^i / (i.factorial : ℝ)) +
          b^17 * 18 / ((Nat.factorial 17 : ℝ) * 17) := by simpa only [Nat.cast_ofNat, show (17 : ℝ) + 1 = 18 by norm_num] using h₂
      _ ≤ _ := by norm_num [b, Finset.sum_range_succ, Nat.factorial]

/-- One rational interval for all the Gaussian weights at the origin, by taking powers. -/
theorem exp_neg_pi_bounds :
    (0.0432139182637 : ℝ) ≤ Real.exp (-Real.pi) ∧
      Real.exp (-Real.pi) ≤ 0.0432139182639 := by
  have he : Real.exp (-Real.pi) = ((Real.exp (Real.pi/4))^4)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]
    norm_num; ring
  have hp := exp_pi_quarter_bounds
  have hL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.1932800507380) hp.1 4
  have hU := pow_le_pow_left₀ (Real.exp_pos _).le hp.2 4
  rw [he]
  exact ⟨(show (0.0432139182637 : ℝ) ≤ ((2.1932800507381 : ℝ)^4)⁻¹ by norm_num).trans
      (inv_anti₀ (by positivity) hU),
    (inv_anti₀ (by positivity) hL).trans
      (show ((2.1932800507380 : ℝ)^4)⁻¹ ≤ 0.0432139182639 by norm_num)⟩

#print axioms exp_neg_pi_bounds

end Nuttall
