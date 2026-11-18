import W5.ThetaGaussianSummability
import W5.ThetaTermIntegrability
import W5.ThetaIntegrandMajorant

/-!
# The two factors of a separable majorant for the theta integral

The n-weight is summable by Gaussian decay; the y-weight is integrable
by the gamma-integral lemma. In combination with
ThetaIntegrandMajorant these are the concrete hypotheses for the
separable Fubini theorem.

This file does not yet state the final interchange of Phi's sum
and improper integral, which requires matching the integrand and
establishing almost-everywhere measurability.
-/

namespace W5

open MeasureTheory

theorem theta_gaussian_weight_summable (y0 : ℝ) (hy0 : 0 < y0) :
    Summable (fun n : ℕ =>
      (5:ℝ) * (n:ℝ)^4 *
        Real.exp (-(n:ℝ)^2 * y0/2)) := by
  have ha : (0:ℝ) < y0/2 := by linarith
  have h := theta_gaussian_polynomial_summable 4 (y0/2) ha
  have hexp (n : ℕ) :
      -(y0/2) * (n:ℝ)^2 = -(n:ℝ)^2 * y0/2 := by ring
  have h' : Summable (fun n : ℕ =>
      (n:ℝ)^4 * Real.exp (-(n:ℝ)^2 * y0/2)) := by
    simpa only [hexp] using h
  simpa only [mul_assoc] using h'.mul_left (5:ℝ)

theorem theta_y_weight_integrableOn (y0 : ℝ) (hy0 : 0 < y0) :
    IntegrableOn
      (fun y : ℝ => y ^ (2:ℝ) * Real.exp (-y/2))
      (Set.Ici y0) volume := by
  have h := theta_rpow_exp_integrableOn_tail
      ((1:ℝ)/2) (2:ℝ) y0 (by norm_num) (by norm_num) hy0
  have heq :
      (fun y : ℝ => y ^ (2:ℝ) * Real.exp (-y/2)) =
      (fun y : ℝ => y ^ (2:ℝ) * Real.exp (-((1:ℝ)/2)*y)) := by
    funext y
    congr 1
    ring
  rw [heq]
  exact h

theorem theta_integrand_abs_split_rpow (p y y0 : ℝ)
    (hp : 1 ≤ p) (hy0 : 1 ≤ y0) (hy : y0 ≤ y) :
    |y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y)| ≤
      (5*p*Real.exp (-p*y0/2)) *
        (y ^ (2:ℝ) * Real.exp (-y/2)) := by
  have hpow : y ^ (2:ℝ) = y ^ (2:ℕ) :=
    Real.rpow_natCast y 2
  rw [hpow]
  exact theta_integrand_abs_split p y y0 hp hy0 hy

end W5
