import Mathlib

/-!
Rigorous uniform ratio constant for the square-index theta tail.
No floating point, no interval oracle and no noncomputable numerical
axiom is used: a nine-term Taylor lower bound for e^15 suffices.
-/
namespace W5

theorem theta_tail_ratio_numerical :
    ((3 : ℝ) / 2) ^ 26 * Real.exp (-15) < (1 : ℝ) / 2 := by
  have htaylor :
      (∑ i ∈ Finset.range 9, (15 : ℝ)^i / (i.factorial : ℝ)) ≤ Real.exp 15 :=
    Real.sum_le_exp_of_nonneg (by norm_num) 9
  have hfinite :
      2 * ((3 : ℝ) / 2)^26 <
        ∑ i ∈ Finset.range 9, (15 : ℝ)^i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hexp : 2 * ((3 : ℝ) / 2)^26 < Real.exp 15 :=
    lt_of_lt_of_le hfinite htaylor
  have hpos : (0 : ℝ) < Real.exp 15 := Real.exp_pos 15
  have hprod : ((3 : ℝ) / 2)^26 < (1/2 : ℝ) * Real.exp 15 := by
    nlinarith [hexp]
  have hdiv : ((3 : ℝ) / 2)^26 / Real.exp 15 < (1/2 : ℝ) :=
    (div_lt_iff₀ hpos).mpr hprod
  rw [Real.exp_neg]
  simpa only [div_eq_mul_inv] using hdiv

theorem n_next_ratio_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) + 1) / (n : ℝ) ≤ (3 : ℝ) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_iff₀ hn0).mpr
  nlinarith

end W5
