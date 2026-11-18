import W5.ThetaExponentialDomination

/-!
# Explicit positive majorant for the theta integrand

For p>=1, y>=y0>=1, the absolute value of the theta integrand
is bounded by a product of:
  * p*exp(-p*y0/2)  (summable for square indices p=n^2),
  * 5*y^2*exp(-y/2) (integrable on [y0,infinity)).

This is the central analytic estimate for termwise integration.
Applying it to the full theta series and the integral still requires
a separate theorem invoking the appropriate dominated-sum principle.
-/

namespace W5

theorem theta_integrand_abs_bound (p y : ℝ)
    (hp : 1 ≤ p) (hy : 1 ≤ y) :
    |y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y)| ≤
      5*p*y^2 * Real.exp (-p*y) := by
  have hy0 : 0 ≤ y := by linarith
  have hpow0 : 0 ≤ y ^ ((1:ℝ)/4) :=
    Real.rpow_nonneg hy0 _
  have hpow : y ^ ((1:ℝ)/4) ≤ y := by
    calc
      y ^ ((1:ℝ)/4) ≤ y ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
      _ = y := by simp
  have hpy : (1:ℝ) ≤ p*y := by
    have hprod : 0 ≤ (p-1)*(y-1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hval : |2*p*y-3| ≤ 5*p*y := by
    apply abs_le.mpr
    constructor <;> nlinarith
  calc
    |y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y)| =
        y ^ ((1:ℝ)/4) * |2*p*y-3| * Real.exp (-p*y) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hpow0,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ y * (5*p*y) * Real.exp (-p*y) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
      exact mul_le_mul hpow hval (abs_nonneg _) hy0
    _ = 5*p*y^2 * Real.exp (-p*y) := by ring

theorem theta_integrand_abs_split (p y y0 : ℝ)
    (hp : 1 ≤ p) (hy0 : 1 ≤ y0) (hy : y0 ≤ y) :
    |y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y)| ≤
      (5*p*Real.exp (-p*y0/2)) *
        (y^2 * Real.exp (-y/2)) := by
  have hy1 : 1 ≤ y := le_trans hy0 hy
  have hbase := theta_integrand_abs_bound p y hp hy1
  have hsplit := theta_exp_split_bound p y y0 hp (by linarith) hy
  calc
    |y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y)| ≤
      5*p*y^2*Real.exp (-p*y) := hbase
    _ ≤ (5*p*y^2) * (Real.exp (-p*y0/2) * Real.exp (-y/2)) := by
      exact mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = (5*p*Real.exp (-p*y0/2)) *
        (y^2*Real.exp (-y/2)) := by ring

end W5
