import W5.ThetaArbitraryPolynomialGaussianSummability

/-!
# ALL 25 original numerical theta elementary base series are summable

The per-entry B00, B10, B11, B02 base summability proofs were
manual expansions into n², n⁴, n⁶ terms. We replace them with
one universal argument:

1. The original finite coefficient polynomial B_ij((p-1)/x,p)
   is explicitly evaluated as an ordinary Polynomial ℝ in p.
   This identity holds for all i,j:Fin 5, x,p∈ℝ.
2. The existing generic Mathlib polynomial/Gaussian theorem
   proves absolute summability of n² exp(-(n²-1)/x²) P(n²)
   for ANY Polynomial ℝ, x>0.

Therefore every original thetaCertificateBaseTerm x i j is
summable for 0<x, not only the previously handled low-order
entries. No new estimates, expansion into monomials for
individual cases or explicit 25-by-25 reasoning is necessary.

The integral corrections, transformed normalized Nuttall
kernel and determinant signs are separate analytic problems.
-/

namespace W5

/-- Exact unintegrated original B_ij coefficient represented as
a finite real polynomial in p=n². All denominators depend on the
fixed x and finite factorials, not on p. -/
noncomputable def thetaCertificateBasePolynomial
    (x : ℝ) (i j : Fin 5) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (min i.val j.val + 1),
    Polynomial.C
      (((-1:ℝ) ^ (i.val + j.val - k)) /
        ((Nat.factorial k : ℝ) *
         (Nat.factorial (i.val-k) : ℝ) *
         (Nat.factorial (j.val-k) : ℝ))) *
    (((Polynomial.X - Polynomial.C (1:ℝ)) *
      Polynomial.C (1/x)) ^ (i.val+j.val-2*k)) *
    Polynomial.X ^ k

/-- The formal polynomial P_ij(x)(p) evaluates to the exact
original coefficient polynomial B_ij((p-1)/x,p). This is purely
algebraic and holds even when x=0, since both expressions
use the same totalized field division convention. -/
theorem thetaCertificateBasePolynomial_eval
    (x p : ℝ) (i j : Fin 5) :
    (thetaCertificateBasePolynomial x i j).eval p =
      coefficientPolynomial i j ((p-1)/x) p := by
  unfold thetaCertificateBasePolynomial coefficientPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  simp only [div_eq_mul_inv]
  ring

/-- At EVERY natural-number square index including n=0,
the original elementary certificate term is precisely the
Gaussian-weighted evaluation of this finite polynomial. -/
theorem thetaCertificateBaseTerm_eq_polynomial_gaussian
    (x : ℝ) (i j : Fin 5) (n : ℕ) :
    thetaCertificateBaseTerm x i j n =
      ((n:ℝ)^2) * Real.exp (-((n:ℝ)^2-1)/x^2) *
        (thetaCertificateBasePolynomial x i j).eval ((n:ℝ)^2) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateBaseTerm]
  · simp only [thetaCertificateBaseTerm, if_neg hn]
    rw [thetaCertificateBasePolynomial_eval]

/-- This SINGLE theorem establishes the separately absolute
summability of ALL original numerical theta base coefficients
i,j:Fin 5 at once for every positive x. The previous
special-case Gaussian-polynomial expansions can be bypassed
for all remaining entries. -/
theorem thetaCertificateBaseTerm_all_summable
    (x : ℝ) (hx : 0 < x) (i j : Fin 5) :
    Summable (fun n : ℕ => thetaCertificateBaseTerm x i j n) := by
  have hfun :
      (fun n : ℕ => thetaCertificateBaseTerm x i j n) =
      (fun n : ℕ =>
        ((n:ℝ)^2) * Real.exp (-((n:ℝ)^2-1)/x^2) *
          (thetaCertificateBasePolynomial x i j).eval ((n:ℝ)^2)) := by
    funext n
    exact thetaCertificateBaseTerm_eq_polynomial_gaussian x i j n
  rw [hfun]
  exact thetaGaussian_original_base_polynomial_summable
    (thetaCertificateBasePolynomial x i j) x hx

end W5
