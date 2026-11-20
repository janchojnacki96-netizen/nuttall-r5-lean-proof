import W5.ThetaMathlibLocalTwoVariableDerivative
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# One Mathlib polynomial theorem replaces numerous separate Gaussian convergence proofs

The existing B00, B10, B11 and B02 proofs each expanded the
elementary square-index theta coefficient into separate powers
of n² and invoked the Gaussian-polynomial summability result.

We instead apply Mathlib's *already proved* finite-polynomial
identity `Polynomial.eval_eq_sum`, and the Mathlib finite-sum
summability lemma. This gives one general theorem:

  for ANY real polynomial P and ANY c>0,
    ∑ n P(n²) exp(-c n²)  converges absolutely.

A corollary handles precisely the shifted original theta
Gaussian factor n² exp(-(n²-1)/x²) times ANY polynomial in n²,
for every x>0. This avoids repeating a separate n²/n⁴/...
convergence proof for each of the remaining matrix entries.

The remaining nontrivial obligation is to *construct and
identify* the polynomial P for the original general B_ij
coefficient. This file does not assume such an identity,
nor assert determinant signs.
-/

namespace W5

/-- Any fixed real polynomial in n² is summable after the
existing strictly positive Gaussian square-index damping. -/
theorem thetaGaussian_arbitrary_polynomial_summable
    (P : Polynomial ℝ) (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ =>
      P.eval ((n:ℝ)^2) * Real.exp (-c*(n:ℝ)^2)) := by
  classical
  have hs (k : ℕ) :
      Summable (fun n : ℕ =>
        (P.coeff k * ((n:ℝ)^2)^k) *
          Real.exp (-c*(n:ℝ)^2)) := by
    have h := theta_gaussian_polynomial_summable (2*k) c hc
    have heq :
        (fun n : ℕ =>
          (P.coeff k * ((n:ℝ)^2)^k) * Real.exp (-c*(n:ℝ)^2)) =
        (fun n : ℕ =>
          P.coeff k * ((n:ℝ)^(2*k) * Real.exp (-c*(n:ℝ)^2))) := by
      funext n
      rw [pow_mul]
      ring
    rw [heq]
    exact h.mul_left (P.coeff k)
  have hsum : Summable (fun n : ℕ =>
      ∑ k ∈ P.support,
        (P.coeff k * ((n:ℝ)^2)^k) *
          Real.exp (-c*(n:ℝ)^2)) := by
    simpa only [Finset.sum_apply] using
      (summable_sum (s := P.support) (fun k _ => hs k))
  have hfun :
      (fun n : ℕ =>
        P.eval ((n:ℝ)^2) * Real.exp (-c*(n:ℝ)^2)) =
      (fun n : ℕ =>
        ∑ k ∈ P.support,
          (P.coeff k * ((n:ℝ)^2)^k) *
            Real.exp (-c*(n:ℝ)^2)) := by
    funext n
    rw [Polynomial.eval_eq_sum]
    change (∑ k ∈ P.support, P.coeff k * ((n:ℝ)^2)^k) *
        Real.exp (-c*(n:ℝ)^2) = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfun]
  exact hsum

/-- All polynomial original theta BASE terms are summable,
with the exact n² factor and shifted Gaussian exponent
exp(-(n²-1)/x²). This theorem simultaneously supplies the
convergence mechanism needed for ALL 25 theta coefficients
as soon as their finite polynomial identity is checked. -/
theorem thetaGaussian_original_base_polynomial_summable
    (P : Polynomial ℝ) (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ =>
      ((n:ℝ)^2) * Real.exp (-((n:ℝ)^2-1)/x^2) *
        P.eval ((n:ℝ)^2)) := by
  let c : ℝ := (1:ℝ)/x^2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hg := thetaGaussian_arbitrary_polynomial_summable
    (Polynomial.X * P) c hc
  have hfun :
      (fun n : ℕ =>
        ((n:ℝ)^2) * Real.exp (-((n:ℝ)^2-1)/x^2) *
          P.eval ((n:ℝ)^2)) =
      (fun n : ℕ =>
        Real.exp c *
          ((Polynomial.X * P).eval ((n:ℝ)^2) *
            Real.exp (-c*(n:ℝ)^2))) := by
    funext n
    have hexp :
        Real.exp (-((n:ℝ)^2-1)/x^2) =
          Real.exp c * Real.exp (-c*(n:ℝ)^2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [c]
      ring
    rw [hexp]
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    ring
  rw [hfun]
  exact hg.mul_left (Real.exp c)

end W5
