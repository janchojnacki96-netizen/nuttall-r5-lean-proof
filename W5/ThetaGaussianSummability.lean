import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gaussian summability with arbitrary polynomial weights

This is the precise index-summability ingredient behind the theta
series: for a>0 and any natural exponent k, the series
  sum_(n>=0) n^k exp(-a*n²)
converges absolutely. It follows by comparison with Mathlib's
linear-exponential summability lemma. This does not yet establish
the interchange of the n-series with improper integration.
-/

namespace W5

private theorem nat_cast_le_square (n : ℕ) :
    (n : ℝ) ≤ (n : ℝ)^2 := by
  cases n with
  | zero => norm_num
  | succ m =>
    have h1 : (1:ℝ) ≤ (Nat.succ m : ℕ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
    have h0 : (0:ℝ) ≤ (Nat.succ m : ℕ) := by positivity
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- The theta-square index admits an integrable Gaussian-polynomial majorant. -/
theorem theta_gaussian_polynomial_summable (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => (n : ℝ)^k * Real.exp (-a * (n : ℝ)^2)) := by
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ)^k * Real.exp (-a * (n : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul k ha
  apply hbase.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hn : (n:ℝ) ≤ (n:ℝ)^2 := nat_cast_le_square n
    have hneg : -a * (n:ℝ)^2 ≤ -a * (n:ℝ) :=
      mul_le_mul_of_nonpos_left hn (by linarith)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hneg) (by positivity)

end W5
