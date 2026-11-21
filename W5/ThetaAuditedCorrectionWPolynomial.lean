import W5.ThetaAuditedTailRationalEnclosure

/-!
# Original theta correction polynomial in the integration variable w

The certificate's actual correction integrand contains
 B_ij(d+w*x, p+w*x^2)
where B_ij is the original degree-at-most-eight Gaussian
coefficient polynomial. Instead of duplicating its 25 formulae
or the integer auditor's binomial expansion, represent this
expression uniformly as an ordinary Mathlib Polynomial R in w.

The exact evaluation theorem reuses Mathlib's polynomial
finset sum/evaluation laws and ring normalization. This is
the analytic-to-algebraic bridge for the finite weighted moments
computed by the 768-bit auditor, not an assumed numeric bound.
-/

namespace W5

/-- Exact original B_ij after the affine substitution used inside
the weighted correction integral. The parameters x,p,d need
no positivity assumptions: this is purely polynomial algebra. -/
noncomputable def thetaCorrectionWPolynomial
    (x p d : ℝ) (i j : Fin 5) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (min i.val j.val + 1),
    Polynomial.C
      (((-1 : ℝ) ^ (i.val+j.val-k)) /
        ((Nat.factorial k : ℝ) *
         (Nat.factorial (i.val-k) : ℝ) *
         (Nat.factorial (j.val-k) : ℝ))) *
      (Polynomial.C d + Polynomial.C x * Polynomial.X) ^
        (i.val+j.val-2*k) *
      (Polynomial.C p + Polynomial.C (x^2) * Polynomial.X)^k

/-- The actual coefficient under EVERY original theta integral
is EXACTLY the value of the new polynomial in w, without
approximation or any assumption about x,p,d,w. -/
theorem thetaCorrectionWPolynomial_eval
    (x p d w : ℝ) (i j : Fin 5) :
    (thetaCorrectionWPolynomial x p d i j).eval w =
      coefficientPolynomial i j (d+w*x) (p+w*x^2) := by
  unfold thetaCorrectionWPolynomial coefficientPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  simp only [div_eq_mul_inv]
  ring

/-- Specialization to the first nonzero square index p=1,d=0:
the integral correction is an exact polynomial-weighted
Lebesgue integral, with no external Gaussian factor. -/
theorem thetaAuditedSeriesTerm_one_polynomial_integral
    (x : ℝ) (i j : Fin 5) :
    thetaAuditedSeriesTerm x i j 1 =
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) -
      (x^2/4) *
        (∫ w in Set.Ici (0 : ℝ),
          Real.exp (-w) *
            (1+w*x^2)^((1 : ℝ)/4) *
              (thetaCorrectionWPolynomial x 1 0 i j).eval w
          ∂MeasureTheory.volume) := by
  rw [thetaAuditedSeriesTerm_one_diagonal_minus_integral]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with w
  rw [thetaCorrectionWPolynomial_eval]

end W5
