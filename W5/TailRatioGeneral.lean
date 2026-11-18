import W5.TailExponentialRatio

/-!
The uniform analytic ratio bound underlying the n>=2 theta-series
tail. This proves a statement about the explicit MAJORANT, not
about the complete theta coefficients or the soundness of the
C++ interval numerical output.
-/
namespace W5

private theorem exponential_step (n y : ℝ) (hn : 2 ≤ n) (hy : 3 ≤ y) :
    Real.exp (-(((n+1)^2-1)*y)) ≤
      Real.exp (-15) * Real.exp (-((n^2-1)*y)) := by
  have h1 : 0 ≤ 2*n-4 := by linarith
  have h2 : 0 ≤ y-3 := by linarith
  have hprod : 0 ≤ (2*n-4)*(y-3) := mul_nonneg h1 h2
  have hdiff : 15 ≤ (2*n+1)*y := by nlinarith [hprod]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem theta_majorant_ratio (n y : ℝ) (hn : 2 ≤ n) (hy : 3 ≤ y) :
    (n+1)^26 * Real.exp (-(((n+1)^2-1)*y)) ≤
      ((3:ℝ)/2)^26 * Real.exp (-15) *
        (n^26 * Real.exp (-((n^2-1)*y))) := by
  have hb : n+1 ≤ ((3:ℝ)/2)*n := by nlinarith
  have hp : (n+1)^26 ≤ (((3:ℝ)/2)*n)^26 := by
    gcongr <;> linarith
  have he := exponential_step n y hn hy
  calc
    (n+1)^26 * Real.exp (-(((n+1)^2-1)*y)) ≤
        (((3:ℝ)/2)*n)^26 * Real.exp (-(((n+1)^2-1)*y)) := by
      exact mul_le_mul_of_nonneg_right hp (le_of_lt (Real.exp_pos _))
    _ ≤ (((3:ℝ)/2)*n)^26 *
        (Real.exp (-15) * Real.exp (-((n^2-1)*y))) := by
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((3:ℝ)/2)^26 * Real.exp (-15) *
        (n^26 * Real.exp (-((n^2-1)*y))) := by
      rw [mul_pow]
      ring

theorem theta_majorant_half_ratio (n y : ℝ) (hn : 2 ≤ n) (hy : 3 ≤ y) :
    (n+1)^26 * Real.exp (-(((n+1)^2-1)*y)) <
      (1:ℝ)/2 * (n^26 * Real.exp (-((n^2-1)*y))) := by
  have hpos : 0 < n^26 * Real.exp (-((n^2-1)*y)) :=
    mul_pos (pow_pos (by linarith) _) (Real.exp_pos _)
  calc
    (n+1)^26 * Real.exp (-(((n+1)^2-1)*y)) ≤
      (((3:ℝ)/2)^26 * Real.exp (-15)) *
        (n^26 * Real.exp (-((n^2-1)*y))) :=
      theta_majorant_ratio n y hn hy
    _ < ((1:ℝ)/2) * (n^26 * Real.exp (-((n^2-1)*y))) :=
      mul_lt_mul_of_pos_right theta_tail_ratio_numerical hpos

end W5
