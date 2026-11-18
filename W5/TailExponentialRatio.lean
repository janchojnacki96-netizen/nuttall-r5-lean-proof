import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Analysis.Complex.Exponential

/-!
The strict numerical inequality controlling the ratio of successive
theta-series tail majorants. This uses Mathlib's *proof-producing*
dyadic exponential enclosure, not the unverified C++ exp implementation.
-/

namespace W5

theorem theta_tail_ratio_numerical :
    ((3 : ℝ) / 2) ^ 26 * Real.exp (-15) < (1 : ℝ) / 2 := by
  dyadic_interval [prec := 50]

/-- The ratio of consecutive squared integer indices is at most 3/2 for n≥2. -/
theorem n_next_ratio_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) + 1) / (n : ℝ) ≤ (3 : ℝ) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_iff₀ hn0).mpr
  nlinarith

end W5
