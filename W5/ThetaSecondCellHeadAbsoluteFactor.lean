import W5.ThetaSecondCellPositiveCellUpper
import W5.ThetaCertificateBaseCorrectionSplit
import W5.ThetaSeriesPrefixTailEnclosure

/-!
# Reusable absolute-value bridge for the ORIGINAL theta square term

Factor out the actual, positive Gaussian common factor from the
original base-minus-correction coefficient. This reduces the
true n=2,3 term estimate to TWO strictly local scalar tasks:
  * the existing positive finite factorial bound for B_ij,
  * an upper bound for the absolute weighted correction integral.
No sum interchange, repeated determinant algebra, numerical
rounding, or new integral formula is introduced.
-/

namespace W5
open MeasureTheory

/-- Universal nonnegative scalar factoring for base minus
weighted correction, reusing Mathlib abs_sub and abs_mul. -/
theorem thetaHead_abs_difference_factor
    (E p s B I Bmax Imax : ℝ)
    (hE : 0 ≤ E) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hB : |B| ≤ Bmax) (hI : |I| ≤ Imax) :
    |p*E*B - s*E*I| ≤ E*(p*Bmax+s*Imax) := by
  calc
    |p*E*B - s*E*I| ≤ |p*E*B| + |s*E*I| := abs_sub _ _
    _ = E*(p*|B|+s*|I|) := by
      simp only [abs_mul, abs_of_nonneg hp,
        abs_of_nonneg hE, abs_of_nonneg hs]
      ring
    _ ≤ E*(p*Bmax+s*Imax) := by
      apply mul_le_mul_of_nonneg_left _ hE
      exact add_le_add
        (mul_le_mul_of_nonneg_left hB hp)
        (mul_le_mul_of_nonneg_left hI hs)

/-- Genuine n-th original theta term with no numerical
approximations or change of the defining Lebesgue integral.
The only hypotheses are elementary base and integral bounds,
so the Gamma/binomial bridge can be introduced ONCE later. -/
theorem thetaAuditedSeriesTerm_abs_le_of_base_integral
    (x : ℝ) (i j : Fin 5) (n : ℕ) (hn : 0 < n)
    (Bmax Imax : ℝ)
    (hB :
      |coefficientPolynomial i j
        (((n:ℝ)^2-1)/x) ((n:ℝ)^2)| ≤ Bmax)
    (hI :
      |∫ w in Set.Ici (0:ℝ),
         Real.exp (-w) *
           (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4) *
           coefficientPolynomial i j
             ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)
         ∂volume| ≤ Imax) :
    |thetaAuditedSeriesTerm x i j n| ≤
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        ((n:ℝ)^2*Bmax+(x^2/4)*Imax) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hE : 0 ≤ Real.exp (-((n:ℝ)^2-1)/x^2) :=
    Real.exp_nonneg _
  have hp : 0 ≤ (n:ℝ)^2 := by positivity
  have hs : 0 ≤ x^2/4 := by positivity
  have hEq :
      thetaAuditedSeriesTerm x i j n =
        ((n:ℝ)^2)*Real.exp (-((n:ℝ)^2-1)/x^2) *
          coefficientPolynomial i j
            (((n:ℝ)^2-1)/x) ((n:ℝ)^2) -
        (x^2/4)*Real.exp (-((n:ℝ)^2-1)/x^2) *
          (∫ w in Set.Ici (0:ℝ),
            Real.exp (-w) * (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4) *
              coefficientPolynomial i j
                ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)
            ∂volume) := by
    simp [thetaAuditedSeriesTerm, thetaCertificateBaseTerm,
      thetaCertificateCorrectionTerm, hn0]
  rw [hEq]
  exact thetaHead_abs_difference_factor
    (Real.exp (-((n:ℝ)^2-1)/x^2))
    ((n:ℝ)^2) (x^2/4)
    (coefficientPolynomial i j (((n:ℝ)^2-1)/x) ((n:ℝ)^2))
    (∫ w in Set.Ici (0:ℝ),
      Real.exp (-w) * (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4) *
        coefficientPolynomial i j
          ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)
      ∂volume) Bmax Imax hE hp hs hB hI

/-- The base polynomial of each TRUE original n-th theta term is
already controlled by the compiled positive factorial envelope.
No moment, integral, or numerical premise is needed for the base. -/
theorem thetaAuditedBasePolynomial_abs_le_positive_at_cell
    (a b x : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (n : ℕ) (hn : 1 ≤ n) (i j : Fin 5) :
    |coefficientPolynomial i j
        (((n:ℝ)^2-1)/x) ((n:ℝ)^2)| ≤
      thetaCoefficientPositivePolynomial i j
        (((n:ℝ)^2-1)/a) ((n:ℝ)^2) := by
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : (1:ℝ) ≤ (n:ℝ)^2 := by
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  have h :=
    thetaPositivePolynomial_cell_upper a b x ((n:ℝ)^2) 0
      ha hax hxb hp (by norm_num) i j
  simpa only [zero_mul, add_zero] using h

end W5
