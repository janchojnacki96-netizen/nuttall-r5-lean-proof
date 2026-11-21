import W5.ThetaFirstCellGammaUniformCandidate
import W5.VerifiedIntervalPolynomials

/-!
# Real-sound fixed rational polynomial interval evaluation

A missing piece of the original x-cell coefficient certificate is a
way to enclose REAL values of polynomials with rational coefficients
using exact rational intervals.

The existing QInterval Horner checker proves soundness for rational
arguments only. Instead of duplicating its signed multiplication or
Mathlib's finite polynomial evaluation formula, we combine:
  * verified QInterval.mul_containsReal,
  * verified QInterval.finsetSum_containsReal,
  * Mathlib Polynomial.eval₂_eq_sum_range.

This module is general-purpose, and does NOT assume any actual
theta coefficient bound. A later step can instantiate the rational
polynomials arising as the nine coefficients in w of the genuine
two-variable theta correction polynomial.
-/

namespace W5

/-- A rational one-point interval contains its exact real cast. -/
theorem thetaRationalPoint_containsReal (q : ℚ) :
    QInterval.ContainsReal (QInterval.point q) (q : ℝ) := by
  simp [QInterval.ContainsReal, QInterval.point]

/-- Extend the existing rational-interval power checker to REAL
semantics using the already verified four-corner multiplication. -/
theorem thetaRationalIntervalPow_containsReal
    (I : QInterval) (x : ℝ) (hx : QInterval.ContainsReal I x)
    (k : ℕ) :
    QInterval.ContainsReal (QInterval.pow I k) (x^k) := by
  induction k with
  | zero =>
      simpa [QInterval.pow] using
        thetaRationalPoint_containsReal 1
  | succ k ih =>
      simpa only [QInterval.pow, pow_succ] using
        (QInterval.mul_containsReal ih hx)

/-- Finite exact-rational interval evaluation of a rational
polynomial using the existing real-sound interval operations.
The finite fold is over its true Mathlib polynomial degree. -/
def thetaRationalPolynomialInterval
    (p : Polynomial ℚ) (I : QInterval) : QInterval :=
  QInterval.finsetSum (Finset.range (p.natDegree+1))
    (fun k =>
      QInterval.mul
        (QInterval.point (p.coeff k))
        (QInterval.pow I k))

/-- A fully proved REAL-sound enclosure for any rational polynomial
on any rational interval. No floating point or unverified numerical
evaluation; Mathlib gives the exact coefficient-sum identity. -/
theorem thetaRationalPolynomialInterval_containsReal
    (p : Polynomial ℚ) (I : QInterval)
    (x : ℝ) (hx : QInterval.ContainsReal I x) :
    QInterval.ContainsReal
      (thetaRationalPolynomialInterval p I)
      (p.eval₂ (Rat.castHom ℝ) x) := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact QInterval.finsetSum_containsReal
    (Finset.range (p.natDegree + 1))
    (fun k =>
      QInterval.mul
        (QInterval.point (p.coeff k))
        (QInterval.pow I k))
    (fun k => (p.coeff k : ℝ) * x^k)
    (fun k _ =>
      QInterval.mul_containsReal
        (thetaRationalPoint_containsReal (p.coeff k))
        (thetaRationalIntervalPow_containsReal I x hx k))

/-- From a checked rational interval endpoint inclusion one
immediately obtains a REAL uniform rational polynomial bound. -/
theorem thetaRationalPolynomialInterval_bounded
    (p : Polynomial ℚ) (I Target : QInterval)
    (x : ℝ) (hx : QInterval.ContainsReal I x)
    (hlo : Target.lo ≤ (thetaRationalPolynomialInterval p I).lo)
    (hhi : (thetaRationalPolynomialInterval p I).hi ≤ Target.hi) :
    QInterval.ContainsReal Target (p.eval₂ (Rat.castHom ℝ) x) := by
  have h := thetaRationalPolynomialInterval_containsReal p I x hx
  exact ⟨(by exact_mod_cast hlo).trans h.1,
    h.2.trans (by exact_mod_cast hhi)⟩

end W5
