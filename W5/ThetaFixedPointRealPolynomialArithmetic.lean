import W5.ThetaSignedFixedPointMultiplication

/-!
# Sound fixed-point arithmetic for REAL polynomial values

The original theta auditor constructs the 25 coefficients from
polynomials in x, x², a shifted Gaussian parameter and weighted
moments. PR #129 established signed outward-rounded multiplication;
PR #120 established compatibility of signed fixed-point
addition/negation/subtraction with exact rational intervals.

This module composes those previously proved theorems. It supplies
REAL soundness of fixed-point addition, negation, subtraction,
and arbitrary natural-number powers, using the existing
QInterval real-semantic arithmetic and the PR #129 multiplication.

The recursive power is a simple reference implementation, not a
claim that the Python auditor's logarithmic-time binary exponent
produces identical endpoints. No analytic theta coefficient
enclosures, exponential rounding, or moment bounds are assumed.
-/

namespace W5

/-- The fixed-point representation of the exact real constant 1. -/
def FixedIntInterval.one (D : ℤ) : FixedIntInterval :=
  ⟨D, D⟩

/-- The constant 1 has exact rational endpoints at any nonzero scale. -/
theorem FixedIntInterval.one_containsReal
    (D : ℤ) (hD : 0 < D) :
    QInterval.ContainsReal ((FixedIntInterval.one D).asQInterval D) 1 := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  simp [FixedIntInterval.one, FixedIntInterval.asQInterval,
    QInterval.ContainsReal, div_self hDq]

/-- Fixed integer addition encloses the addition of REAL inputs.
Reuse of the exact rational compatibility theorem from #120. -/
theorem FixedIntInterval.add_containsReal
    (D : ℤ) (a b : FixedIntInterval) (x y : ℝ)
    (ha : QInterval.ContainsReal (a.asQInterval D) x)
    (hb : QInterval.ContainsReal (b.asQInterval D) y) :
    QInterval.ContainsReal
      ((a.add b).asQInterval D) (x + y) := by
  rw [FixedIntInterval.asQInterval_add]
  exact QInterval.add_containsReal ha hb

/-- Fixed signed negation encloses real negation with no rounding. -/
theorem FixedIntInterval.neg_containsReal
    (D : ℤ) (a : FixedIntInterval) (x : ℝ)
    (ha : QInterval.ContainsReal (a.asQInterval D) x) :
    QInterval.ContainsReal
      (a.neg.asQInterval D) (-x) := by
  rw [FixedIntInterval.asQInterval_neg]
  exact QInterval.neg_containsReal ha

/-- Fixed signed subtraction encloses real subtraction with no
additional rounding beyond the input intervals. -/
theorem FixedIntInterval.sub_containsReal
    (D : ℤ) (a b : FixedIntInterval) (x y : ℝ)
    (ha : QInterval.ContainsReal (a.asQInterval D) x)
    (hb : QInterval.ContainsReal (b.asQInterval D) y) :
    QInterval.ContainsReal
      ((a.sub b).asQInterval D) (x - y) := by
  rw [FixedIntInterval.asQInterval_sub]
  exact QInterval.sub_containsReal ha hb

/-- Arbitrary natural-number powers using the already proved
signed four-corner outward multiplication. -/
def FixedIntInterval.pow (a : FixedIntInterval) (D : ℤ) :
    ℕ → FixedIntInterval
  | 0 => FixedIntInterval.one D
  | n + 1 => (a.pow D n).mul D a

/-- All natural-number powers of an arbitrary REAL quantity are
enclosed by the fixed-point recursive interval computation.
Crucially no sign assumptions on x or the input endpoints are needed. -/
theorem FixedIntInterval.pow_containsReal
    (D : ℤ) (hD : 0 < D)
    (a : FixedIntInterval) (x : ℝ)
    (ha : QInterval.ContainsReal (a.asQInterval D) x) :
    ∀ n : ℕ,
      QInterval.ContainsReal ((a.pow D n).asQInterval D) (x ^ n) := by
  intro n
  induction n with
  | zero =>
      simpa only [FixedIntInterval.pow, pow_zero] using
        FixedIntInterval.one_containsReal D hD
  | succ n ih =>
      have hs := FixedIntInterval.mul_containsReal
        D hD (a.pow D n) a (x ^ n) x ih ha
      simpa only [FixedIntInterval.pow, pow_succ] using hs

/-- The same real-soundness theorem specialized to the
exact scale used by the independently audited 51 theta cells. -/
theorem FixedIntInterval.auditPow_containsReal
    (a : FixedIntInterval) (x : ℝ)
    (ha : QInterval.ContainsReal
      (a.asQInterval thetaAuditScale) x) (n : ℕ) :
    QInterval.ContainsReal
      ((a.pow thetaAuditScale n).asQInterval thetaAuditScale)
      (x ^ n) :=
  FixedIntInterval.pow_containsReal
    thetaAuditScale thetaAuditScale_pos a x ha n

end W5
