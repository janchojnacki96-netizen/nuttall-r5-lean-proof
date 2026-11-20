import W5.ThetaSquareIndexDecay
import LeanCert.Tactic.IntervalAuto

/-!
# Isolated LeanCert kernel-only integration test

The external interval checker is pinned to a fixed commit and uses
exactly the Lean/Mathlib v4.35.0 toolchain of this project.

The first bound is the quantitative surviving Gaussian decay constant
already used throughout the theta estimates (47/64). The second test
is a real-variable interval bound on a small positive interval,
checked without sampling. Both numerical certificates are reduced
INSIDE the Lean kernel (trust := kernel), never native_decide.

If any test fails, this experiment stays separate from the proven
theta PR chain. No claim about the Wronskian signs is made.
-/

namespace W5

/-- Concrete rigorous theta envelope at the first square index:
exp(-47/64) is strictly below 1/2. -/
theorem leancert_theta_first_gaussian_lt_half :
    Real.exp (-((47:ℝ)/64)) < (1:ℝ)/2 := by
  interval_decide (trust := kernel)

/-- The exponential factor stays above 3/4 on [0,1/4].
This checks a WHOLE interval, not sampled points. -/
theorem leancert_exp_negative_quarter_lower :
    ∀ x ∈ Set.Icc (0:ℝ) (1/4), (3:ℝ)/4 ≤ Real.exp (-x) := by
  certify_bound (trust := kernel)

/-- Lift the quantitative LeanCert bound to EVERY square-index
parameter p≥1, using the monotonicity formalized in Mathlib. -/
theorem leancert_theta_gaussian_decay_lt_half
    (p : ℝ) (hp : 1 ≤ p) :
    Real.exp (-((47:ℝ)/64)*p) < (1:ℝ)/2 := by
  have he : -((47:ℝ)/64)*p ≤ -(47:ℝ)/64 := by
    nlinarith
  exact lt_of_le_of_lt
    (Real.exp_le_exp.mpr he) leancert_theta_first_gaussian_lt_half

#print axioms leancert_theta_first_gaussian_lt_half
#print axioms leancert_exp_negative_quarter_lower
#print axioms leancert_theta_gaussian_decay_lt_half

end W5
