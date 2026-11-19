import W5.ThetaWeightedGaussianMixedJets
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Polynomial-Gaussian index summability and w-tail integrability

Higher right- and mixed-theta jets introduce arbitrarily large
(but fixed-order) polynomial factors in the square index n² and
in the integration variable w.

The two elementary building blocks below are fully quantified
over any natural polynomial degree:
  sum_n (n²)^k exp(-47 n²/64) < infinity,
  integral_{w>0} w^k exp(-w/4) < infinity.

The next analytic task is combining these through finite polynomial
expansions to dominate the genuine higher theta jets, then invoking
Mathlib's dominated derivative-of-integral/sum results.
-/

namespace W5
open MeasureTheory

/-- Every even polynomial index factor is summable under the
surviving Gaussian square-index decay. -/
theorem thetaHigherJet_even_index_monomial_summable (k : ℕ) :
    Summable (fun n : ℕ =>
      ((n:ℝ)^2)^k * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) := by
  have h := theta_gaussian_polynomial_summable
    (2*k) ((47:ℝ)/64) (by norm_num)
  simpa only [pow_mul] using h

/-- Every finite polynomial order remains integrable against
the surviving w-exponential tail on the positive half-line. -/
theorem thetaHigherJet_w_monomial_integrableOn (k : ℕ) :
    IntegrableOn (fun w : ℝ =>
      w^k * Real.exp (-((1:ℝ)/4)*w))
      (Set.Ioi (0:ℝ)) volume := by
  have hk : (-1:ℝ) < (k:ℝ) := by
    have hn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have h : IntegrableOn (fun w : ℝ =>
      w ^ (k:ℝ) * Real.exp (-((1:ℝ)/4)*w^(1:ℝ)))
      (Set.Ioi (0:ℝ)) volume :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p:=(1:ℝ)) (s:=(k:ℝ)) (b:=(1:ℝ)/4)
      hk (by norm_num) (by norm_num)
  simpa only [Real.rpow_natCast, Real.rpow_one] using h

end W5
