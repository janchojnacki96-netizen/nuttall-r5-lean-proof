import W5.VerifiedIntervalMultiplication

/-!
# Verified rational interval reciprocals and safe signed division

The existing original W5 certificate uses 255 signed LDL pivot
tests. Those tests repeatedly divide an interval by an interval
known to be entirely positive or entirely negative.

Instead of writing a bespoke division checker, reuse the proved
four-corner interval multiplication from W5 and Mathlib's
`one_div_le_one_div_of_le` inequality. This yields a sound
division operator for EITHER pivot sign.

No division result is asserted if the denominator interval
contains zero. No approximation, rounding, transcendental
bound, or determinant sign is assumed in this module.
-/

namespace W5.QInterval

/-- Exact rational reciprocal enclosure when the whole interval
lies strictly above zero. -/
def inversePositive (a : QInterval) : QInterval :=
  ⟨(a.hi)⁻¹, (a.lo)⁻¹⟩

/-- For a strictly positive denominator interval, inverting
the endpoints (and reversing their order) encloses 1/x. -/
theorem inversePositive_contains
    {a : QInterval} {x : ℚ}
    (ha : Contains a x) (hlo : 0 < a.lo) :
    Contains (inversePositive a) x⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le hlo ha.1
  constructor
  · simpa [inversePositive, Contains, one_div] using
      (one_div_le_one_div_of_le hx ha.2)
  · simpa [inversePositive, Contains, one_div] using
      (one_div_le_one_div_of_le hlo ha.1)

/-- Negative pivot reciprocals are obtained by exact sign
conjugation of the already verified positive case. -/
def inverseNegative (a : QInterval) : QInterval :=
  neg (inversePositive (neg a))

theorem inverseNegative_contains
    {a : QInterval} {x : ℚ}
    (ha : Contains a x) (hhi : a.hi < 0) :
    Contains (inverseNegative a) x⁻¹ := by
  have hpos : 0 < (neg a).lo := by
    change 0 < -a.hi
    linarith
  have hinv : Contains (inversePositive (neg a)) (-x)⁻¹ :=
    inversePositive_contains (neg_contains ha) hpos
  have hres := neg_contains hinv
  simpa only [inverseNegative, inv_neg, neg_neg] using hres

/-- Choose the appropriate exact reciprocal enclosure by the
sign of the first endpoint. The sign precondition in the
soundness theorem excludes every interval crossing zero. -/
def inverseSigned (a : QInterval) : QInterval :=
  if 0 < a.lo then inversePositive a else inverseNegative a

theorem inverseSigned_contains
    {a : QInterval} {x : ℚ}
    (ha : Contains a x)
    (hsign : 0 < a.lo ∨ a.hi < 0) :
    Contains (inverseSigned a) x⁻¹ := by
  by_cases hp : 0 < a.lo
  · simpa [inverseSigned, hp] using
      (inversePositive_contains ha hp)
  · have hn : a.hi < 0 := hsign.resolve_left hp
    simpa [inverseSigned, hp] using
      (inverseNegative_contains ha hn)

/-- A single rational interval division operation works for
both the positive and negative pivots in the W5 certificate. -/
def divideSigned (a b : QInterval) : QInterval :=
  mul a (inverseSigned b)

/-- Division soundness follows directly from two already
proved enclosure lemmas, not a duplicated sign-case proof. -/
theorem divideSigned_contains
    {a b : QInterval} {x y : ℚ}
    (ha : Contains a x) (hb : Contains b y)
    (hsign : 0 < b.lo ∨ b.hi < 0) :
    Contains (divideSigned a b) (x / y) := by
  simpa only [divideSigned, div_eq_mul_inv] using
    (mul_contains ha (inverseSigned_contains hb hsign))

/-- The original 2-by-2 Schur pivot uses a subtraction
of a product divided by a signed diagonal pivot. This
verified operator composes three sound interval operations. -/
def schurUpdate (a_ij a_ik a_kj pivot : QInterval) : QInterval :=
  sub a_ij (divideSigned (mul a_ik a_kj) pivot)

theorem schurUpdate_contains
    {a_ij a_ik a_kj pivot : QInterval}
    {v_ij v_ik v_kj p : ℚ}
    (hij : Contains a_ij v_ij)
    (hik : Contains a_ik v_ik)
    (hkj : Contains a_kj v_kj)
    (hp : Contains pivot p)
    (hsign : 0 < pivot.lo ∨ pivot.hi < 0) :
    Contains (schurUpdate a_ij a_ik a_kj pivot)
      (v_ij - v_ik * v_kj / p) := by
  exact sub_contains hij
    (divideSigned_contains (mul_contains hik hkj) hp hsign)

end W5.QInterval
