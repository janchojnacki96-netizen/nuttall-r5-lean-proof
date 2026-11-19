import W5.ThetaGaussianUniformDecay
import W5.ThetaTermIntegrability

/-!
# Absolute integrability of polynomial Gaussian envelopes

A local uniform bound for the transformed theta Gaussian was established
by `thetaGaussian_uniform_decay`: the w-dependent part is bounded by
`exp (-w/4)`. The first and second mixed derivatives also introduce
polynomials in w. Here we prove the actual (Lebesgue) integrability of
every power of w multiplied by that common exponential envelope.

These are unconditional integrability theorems for concrete functions.
The domination of the *whole* derivative/infinite-series integrand
and the derivative/integral interchange are separate obligations.
-/

namespace W5
open MeasureTheory

/-- The full family of polynomial-exponential majorants is integrable
on the strictly positive half-line. This suffices for any finite jet
order, once pointwise bounds on the corresponding differentiated
Gaussian factors are established. -/
theorem thetaGaussian_polynomial_exp_integrable (k : ℕ) :
    IntegrableOn
      (fun w : ℝ => w ^ k * Real.exp (-((1:ℝ)/4) * w))
      (Set.Ioi (0:ℝ)) volume := by
  have hk : (-1:ℝ) < (k:ℝ) := by
    have hkn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  simpa only [Real.rpow_natCast] using
    (theta_rpow_exp_integrableOn ((1:ℝ)/4) (k:ℝ)
      (by norm_num) hk)

/-- Any quadratic polynomial times the fixed Gaussian envelope is
absolutely integrable. This directly covers the low-order
`B₁₁(d₀+w*x, p+w*x²)` polynomial after expansion. -/
theorem thetaGaussian_quadratic_exp_integrable (a b c : ℝ) :
    IntegrableOn
      (fun w : ℝ =>
        (a*w^2 + b*w + c) * Real.exp (-((1:ℝ)/4)*w))
      (Set.Ioi (0:ℝ)) volume := by
  have h0 := thetaGaussian_polynomial_exp_integrable 0
  have h1 := thetaGaussian_polynomial_exp_integrable 1
  have h2 := thetaGaussian_polynomial_exp_integrable 2
  have hsum : IntegrableOn
      (fun w : ℝ =>
        a * (w^2 * Real.exp (-((1:ℝ)/4)*w)) +
        b * (w^1 * Real.exp (-((1:ℝ)/4)*w)) +
        c * (w^0 * Real.exp (-((1:ℝ)/4)*w)))
      (Set.Ioi (0:ℝ)) volume :=
    ((h2.const_mul a).add (h1.const_mul b)).add (h0.const_mul c)
  convert hsum using 1
  funext w
  ring

/-- Convenient square-polynomial envelope for the first mixed theta jet. -/
theorem thetaGaussian_one_add_square_exp_integrable :
    IntegrableOn
      (fun w : ℝ => (1+w)^2 * Real.exp (-((1:ℝ)/4)*w))
      (Set.Ioi (0:ℝ)) volume := by
  convert thetaGaussian_quadratic_exp_integrable (1:ℝ) 2 1 using 1
  funext w
  ring


/-- The exact original theta model's mixed Gaussian coefficient has
an integrable polynomial/exponential envelope for every fixed
parameter triple `(d0,p,x)`. The identity used here is the
already-proved genuine mixed derivative formula. -/
theorem thetaGaussian_mixed_coefficient_exp_integrable
    (d0 p x : ℝ) :
    IntegrableOn
      (fun w : ℝ =>
        gaussianMixedCoeff11 (d0+w*x) (p+w*x^2) *
          Real.exp (-((1:ℝ)/4)*w))
      (Set.Ioi (0:ℝ)) volume := by
  convert thetaGaussian_quadratic_exp_integrable
      (x^2) (2*d0*x-x^2) (d0^2-p) using 1
  funext w
  rw [gaussianMixedCoeff11_exact]
  ring

end W5
