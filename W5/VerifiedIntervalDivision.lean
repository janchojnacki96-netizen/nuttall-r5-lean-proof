import W5.VerifiedIntervalMultiplication

/-!
# Exact rational interval reciprocals and division

The 768-bit fixed-point checker uses interval reciprocals during
LDL pivot elimination. Here we formalize the underlying exact-rational
enclosures, for intervals strictly on either side of zero.

This is sound rational interval arithmetic, NOT yet a proof of
rounding correctness for the concrete 768-bit implementation.
-/

namespace W5.QInterval

/-- Reciprocal enclosure for a strictly positive interval. -/
def reciprocalPositive (a : QInterval) : QInterval :=
  ⟨1 / a.hi, 1 / a.lo⟩

theorem reciprocalPositive_contains {a : QInterval} {x : ℚ}
    (hlo : 0 < a.lo) (ha : Contains a x) :
    Contains (reciprocalPositive a) (1 / x) := by
  have hx : 0 < x := lt_of_lt_of_le hlo ha.1
  have hhi : 0 < a.hi := lt_of_lt_of_le hx ha.2
  change (1 : ℚ) / a.hi ≤ 1 / x ∧ 1 / x ≤ 1 / a.lo
  constructor
  · apply (div_le_div_iff₀ hhi hx).2
    simpa only [one_mul] using ha.2
  · apply (div_le_div_iff₀ hx hlo).2
    simpa only [one_mul] using ha.1

/-- The negative interval is first reflected into a positive one. -/
def reciprocalNegative (a : QInterval) : QInterval :=
  neg (reciprocalPositive (neg a))

theorem reciprocalNegative_contains {a : QInterval} {x : ℚ}
    (hhi : a.hi < 0) (ha : Contains a x) :
    Contains (reciprocalNegative a) (1 / x) := by
  have hpos : 0 < (neg a).lo := by
    change 0 < -a.hi
    linarith
  have hn : Contains (neg a) (-x) := neg_contains ha
  have hrec := reciprocalPositive_contains hpos hn
  have hrecneg := neg_contains hrec
  simpa [reciprocalNegative] using hrecneg

/-- Exact-rational interval division by positive denominator bounds. -/
def divPositive (a b : QInterval) : QInterval :=
  mul a (reciprocalPositive b)

/-- The usual quotient belongs to the computed interval, even when
the numerator interval contains negative and positive values. -/
theorem divPositive_contains {a b : QInterval} {x y : ℚ}
    (ha : Contains a x) (hb : Contains b y) (hbpos : 0 < b.lo) :
    Contains (divPositive a b) (x / y) := by
  simpa only [divPositive, div_eq_mul_inv, one_div, one_mul] using
    mul_contains ha (reciprocalPositive_contains hbpos hb)

/-- Exact-rational interval division by negative denominator bounds. -/
def divNegative (a b : QInterval) : QInterval :=
  mul a (reciprocalNegative b)

theorem divNegative_contains {a b : QInterval} {x y : ℚ}
    (ha : Contains a x) (hb : Contains b y) (hbneg : b.hi < 0) :
    Contains (divNegative a b) (x / y) := by
  simpa only [divNegative, div_eq_mul_inv, one_div, one_mul] using
    mul_contains ha (reciprocalNegative_contains hbneg hb)

end W5.QInterval
