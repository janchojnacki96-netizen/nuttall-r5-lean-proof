import W5.DirectedRounding
import W5.VerifiedIntervalCore

/-!
# Integer-scaled rational interval arithmetic for the 768-bit audit

The independent certificate stores `[lo,hi]` as exact integers
representing rational endpoints `lo / 2^768`, `hi / 2^768`.

The project already proves outward integer Euclidean rounding:
`int_ediv_le_rat_div` and `rat_div_le_int_ceil`.
This module reuses those theorems directly, rather than rewriting
Euclidean division inequalities or relying on floating point.

It also proves that exact fixed-scale integer addition, negation and
subtraction agree with the ALREADY verified QInterval operations.
Signed integer multiplication is safely rounded outwards by the
existing generic division lemmas.

This is infrastructure for formal verification of the 768-bit Python
certificate; it is not an assertion that all theta enclosures or 255
pivot signs have been supplied in Lean.
-/

namespace W5

structure FixedIntInterval where
  lo : ℤ
  hi : ℤ
deriving Repr, DecidableEq

/-- Interpret a pair of scaled integers as an exact rational interval. -/
def FixedIntInterval.asQInterval (D : ℤ) (a : FixedIntInterval) :
    QInterval :=
  ⟨(a.lo : ℚ) / (D : ℚ), (a.hi : ℚ) / (D : ℚ)⟩

/-- Addition needs no rounding when both operands use the same scale. -/
def FixedIntInterval.add (a b : FixedIntInterval) :
    FixedIntInterval :=
  ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Negation reverses endpoints, including negative intervals. -/
def FixedIntInterval.neg (a : FixedIntInterval) :
    FixedIntInterval :=
  ⟨-a.hi, -a.lo⟩

/-- Subtraction is addition of the reflected interval. -/
def FixedIntInterval.sub (a b : FixedIntInterval) :
    FixedIntInterval :=
  add a (neg b)

/-- Exact compatibility of integer-scaled addition with the proved
rational interval addition; no range/positivity hypothesis is needed. -/
theorem FixedIntInterval.asQInterval_add
    (D : ℤ) (a b : FixedIntInterval) :
    (FixedIntInterval.add a b).asQInterval D =
      QInterval.add (a.asQInterval D) (b.asQInterval D) := by
  cases a with
  | mk alo ahi =>
    cases b with
    | mk blo bhi =>
      simp [FixedIntInterval.add, FixedIntInterval.asQInterval,
        QInterval.add, Int.cast_add, add_div]

/-- Exact compatibility of negation with the proved rational
interval negation, including sign reversal of both endpoints. -/
theorem FixedIntInterval.asQInterval_neg
    (D : ℤ) (a : FixedIntInterval) :
    (FixedIntInterval.neg a).asQInterval D =
      QInterval.neg (a.asQInterval D) := by
  cases a with
  | mk alo ahi =>
    simp [FixedIntInterval.neg, FixedIntInterval.asQInterval,
      QInterval.neg, Int.cast_neg, neg_div]

/-- Exact compatibility of subtraction with already proved
rational interval subtraction. -/
theorem FixedIntInterval.asQInterval_sub
    (D : ℤ) (a b : FixedIntInterval) :
    (FixedIntInterval.sub a b).asQInterval D =
      QInterval.sub (a.asQInterval D) (b.asQInterval D) := by
  rw [FixedIntInterval.sub, FixedIntInterval.asQInterval_add,
    FixedIntInterval.asQInterval_neg]
  rfl

/-- Addition of two certified scaled integer intervals encloses the
sum, by reuse of the existing exact QInterval soundness theorem. -/
theorem FixedIntInterval.add_contains
    (D : ℤ) (a b : FixedIntInterval) (x y : ℚ)
    (ha : QInterval.Contains (a.asQInterval D) x)
    (hb : QInterval.Contains (b.asQInterval D) y) :
    QInterval.Contains ((FixedIntInterval.add a b).asQInterval D)
      (x + y) := by
  rw [FixedIntInterval.asQInterval_add]
  exact QInterval.add_contains ha hb

/-- Signed integer Euclidean floor/ceiling both enclose the
exact rational quotient, independent of the sign of the numerator. -/
theorem fixedIntegerQuotient_rounds_outward
    (a D : ℤ) (hD : 0 < D) :
    ((a / D : ℤ) : ℚ) ≤ (a : ℚ) / (D : ℚ) ∧
      (a : ℚ) / (D : ℚ) ≤
        ((-((-a) / D : ℤ) : ℤ) : ℚ) :=
  ⟨int_ediv_le_rat_div a D hD, rat_div_le_int_ceil a D hD⟩

/-- In particular a *signed* product divided by the scale is
outward-rounded by the same two integer operations. This is the
fundamental correctness statement used for each of the four endpoint
products in a 768-bit interval multiplication. -/
theorem fixedIntegerProduct_rounds_outward
    (a b D : ℤ) (hD : 0 < D) :
    (((a * b) / D : ℤ) : ℚ) ≤
      (a : ℚ) * (b : ℚ) / (D : ℚ) ∧
    (a : ℚ) * (b : ℚ) / (D : ℚ) ≤
      ((-((-(a * b)) / D : ℤ) : ℤ) : ℚ) := by
  simpa only [Int.cast_mul] using
    (fixedIntegerQuotient_rounds_outward (a*b) D hD)

/-- The exact scale used by the independent integer certificate. -/
def thetaAuditScale : ℤ := 2 ^ 768

theorem thetaAuditScale_pos : (0 : ℤ) < thetaAuditScale := by
  unfold thetaAuditScale
  positivity

/-- The preceding signed-product rounding lemma, specialized to
the genuine 768-bit fixed-point audit scale. -/
theorem thetaAuditProduct_rounds_outward (a b : ℤ) :
    (((a*b) / thetaAuditScale : ℤ) : ℚ) ≤
      (a : ℚ) * (b : ℚ) / (thetaAuditScale : ℚ) ∧
    (a : ℚ) * (b : ℚ) / (thetaAuditScale : ℚ) ≤
      ((-((-(a*b)) / thetaAuditScale : ℤ) : ℤ) : ℚ) :=
  fixedIntegerProduct_rounds_outward a b thetaAuditScale
    thetaAuditScale_pos

end W5
