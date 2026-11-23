import W5.ThetaSecondCellPositivePolynomial
import W5.ThetaAllSquareIndexNineMoments

/-!
# Positive affine theta polynomial in the integration variable

The original B_ij coefficient is bounded by a positive factorial
polynomial in the two affine expressions D+b*w and p+b²*w.
Represent that polynomial ONCE as a genuine Mathlib Polynomial ℝ
and reuse the ALREADY proved weighted-polynomial moment identity.

The evaluation identity is pure polynomial algebra. In the next
step the existing thetaWeightedPolynomialIntegral_eq_coeffSum
allows its genuine weighted Lebesgue integral to be expressed as
a finite set of Gamma moments, rather than redoing integration.
-/

namespace W5

/-- The exact positive factorial envelope, viewed as an
ordinary polynomial in the original integration variable w. -/
noncomputable def thetaHeadPositiveWPolynomial
    (D p b : ℝ) (i j : Fin 5) : Polynomial ℝ :=
  ∑ t ∈ Finset.range (min i.val j.val + 1),
    Polynomial.C
      (1 / ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))) *
      (Polynomial.C D + Polynomial.C b * Polynomial.X)^(i.val+j.val-2*t) *
      (Polynomial.C p + Polynomial.C (b^2) * Polynomial.X)^t

/-- One identity for all 25 genuine coefficient envelopes:
the positive polynomial from the original derivative formula
equals the evaluation of this explicit Mathlib polynomial. -/
theorem thetaHeadPositiveWPolynomial_eval
    (D p b w : ℝ) (i j : Fin 5) :
    (thetaHeadPositiveWPolynomial D p b i j).eval w =
      thetaCoefficientPositivePolynomial i j
        (D+w*b) (p+w*b^2) := by
  classical
  unfold thetaHeadPositiveWPolynomial
    thetaCoefficientPositivePolynomial
  simp only [map_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro t ht
  ring

end W5
