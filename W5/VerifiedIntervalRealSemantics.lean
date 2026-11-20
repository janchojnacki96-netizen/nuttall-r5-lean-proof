import W5.VerifiedIntervalDivision

/-!
# Exact rational endpoints enclosing REAL theta matrix entries

The previously certified interval library bounds rational values.
The real theta coefficients are transcendental, so we need a theorem
that the SAME finitely-computable rational endpoints also enclose
REAL values under every arithmetic step. This module proves that
the exact interval add/neg/mul/div and Schur-update operations are
sound when applied to real values.

We reuse:
* the existing exact rational four-corner multiplication definition;
* Mathlib's ordered-field monotonicity lemmas;
* Mathlib's rational-to-real ring homomorphism.

This is a semantics bridge, not a replacement of the original
certified theta entry estimates. Those estimates must STILL
supply interval enclosures for the actual transcendental entries.
-/

namespace W5.QInterval

/-- A computable rational interval interpreted as a closed
REAL interval. The stored endpoints remain exact rationals. -/
def ContainsReal (a : QInterval) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

/-- Exact rational interval addition is sound on REAL values. -/
theorem add_containsReal
    {a b : QInterval} {x y : ℝ}
    (ha : ContainsReal a x) (hb : ContainsReal b y) :
    ContainsReal (add a b) (x+y) := by
  simpa only [ContainsReal, add, Rat.cast_add] using
    (show ((a.lo:ℝ)+(b.lo:ℝ) ≤ x+y) ∧
       (x+y ≤ (a.hi:ℝ)+(b.hi:ℝ)) from
      ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩)

/-- Exact rational endpoint negation is sound on REAL values. -/
theorem neg_containsReal
    {a : QInterval} {x : ℝ}
    (ha : ContainsReal a x) :
    ContainsReal (neg a) (-x) := by
  simpa only [ContainsReal, neg, Rat.cast_neg] using
    (show -((a.hi:ℝ)) ≤ -x ∧ -x ≤ -((a.lo:ℝ)) from
      ⟨neg_le_neg ha.2, neg_le_neg ha.1⟩)

/-- Subtraction is a composition of two already checked
real-semantic interval operations. -/
theorem sub_containsReal
    {a b : QInterval} {x y : ℝ}
    (ha : ContainsReal a x) (hb : ContainsReal b y) :
    ContainsReal (sub a b) (x-y) := by
  simpa only [sub, sub_eq_add_neg] using
    add_containsReal ha (neg_containsReal hb)

/-- Mathlib's rational-to-real ordered embedding transfers
the EXACT four-corner bounds from the rational checker. This
lemma treats all possible endpoint signs, not only positive
intervals. -/
theorem mul_containsReal
    {a b : QInterval} {x y : ℝ}
    (ha : ContainsReal a x) (hb : ContainsReal b y) :
    ContainsReal (mul a b) (x*y) := by
  have hll : ((mul a b).lo : ℝ) ≤ (a.lo:ℝ)*(b.lo:ℝ) := by
    have hq : (mul a b).lo ≤ a.lo*b.lo :=
      (min_le_left _ _).trans (min_le_left _ _)
    exact_mod_cast hq
  have hlh : ((mul a b).lo : ℝ) ≤ (a.lo:ℝ)*(b.hi:ℝ) := by
    have hq : (mul a b).lo ≤ a.lo*b.hi :=
      (min_le_left _ _).trans (min_le_right _ _)
    exact_mod_cast hq
  have hhl : ((mul a b).lo : ℝ) ≤ (a.hi:ℝ)*(b.lo:ℝ) := by
    have hq : (mul a b).lo ≤ a.hi*b.lo :=
      (min_le_right _ _).trans (min_le_left _ _)
    exact_mod_cast hq
  have hhh : ((mul a b).lo : ℝ) ≤ (a.hi:ℝ)*(b.hi:ℝ) := by
    have hq : (mul a b).lo ≤ a.hi*b.hi :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact_mod_cast hq
  have hllhi : (a.lo:ℝ)*(b.lo:ℝ) ≤ ((mul a b).hi:ℝ) := by
    have hq : a.lo*b.lo ≤ (mul a b).hi :=
      (le_max_left _ _).trans (le_max_left _ _)
    exact_mod_cast hq
  have hlhhi : (a.lo:ℝ)*(b.hi:ℝ) ≤ ((mul a b).hi:ℝ) := by
    have hq : a.lo*b.hi ≤ (mul a b).hi :=
      (le_max_right _ _).trans (le_max_left _ _)
    exact_mod_cast hq
  have hhlhi : (a.hi:ℝ)*(b.lo:ℝ) ≤ ((mul a b).hi:ℝ) := by
    have hq : a.hi*b.lo ≤ (mul a b).hi :=
      (le_max_left _ _).trans (le_max_right _ _)
    exact_mod_cast hq
  have hhhhi : (a.hi:ℝ)*(b.hi:ℝ) ≤ ((mul a b).hi:ℝ) := by
    have hq : a.hi*b.hi ≤ (mul a b).hi :=
      (le_max_right _ _).trans (le_max_right _ _)
    exact_mod_cast hq
  constructor
  · by_cases hx : 0 ≤ x
    · by_cases hbl : 0 ≤ (b.lo:ℝ)
      · calc
          ((mul a b).lo:ℝ) ≤ (a.lo:ℝ)*(b.lo:ℝ) := hll
          _ ≤ x*(b.lo:ℝ) := mul_le_mul_of_nonneg_right ha.1 hbl
          _ ≤ x*y := mul_le_mul_of_nonneg_left hb.1 hx
      · have hbl' : (b.lo:ℝ) ≤ 0 := le_of_lt (lt_of_not_ge hbl)
        calc
          ((mul a b).lo:ℝ) ≤ (a.hi:ℝ)*(b.lo:ℝ) := hhl
          _ ≤ x*(b.lo:ℝ) := mul_le_mul_of_nonpos_right ha.2 hbl'
          _ ≤ x*y := mul_le_mul_of_nonneg_left hb.1 hx
    · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      by_cases hbh : 0 ≤ (b.hi:ℝ)
      · calc
          ((mul a b).lo:ℝ) ≤ (a.lo:ℝ)*(b.hi:ℝ) := hlh
          _ ≤ x*(b.hi:ℝ) := mul_le_mul_of_nonneg_right ha.1 hbh
          _ ≤ x*y := mul_le_mul_of_nonpos_left hb.2 hx'
      · have hbh' : (b.hi:ℝ) ≤ 0 := le_of_lt (lt_of_not_ge hbh)
        calc
          ((mul a b).lo:ℝ) ≤ (a.hi:ℝ)*(b.hi:ℝ) := hhh
          _ ≤ x*(b.hi:ℝ) := mul_le_mul_of_nonpos_right ha.2 hbh'
          _ ≤ x*y := mul_le_mul_of_nonpos_left hb.2 hx'
  · by_cases hx : 0 ≤ x
    · by_cases hbh : 0 ≤ (b.hi:ℝ)
      · calc
          x*y ≤ x*(b.hi:ℝ) := mul_le_mul_of_nonneg_left hb.2 hx
          _ ≤ (a.hi:ℝ)*(b.hi:ℝ) := mul_le_mul_of_nonneg_right ha.2 hbh
          _ ≤ ((mul a b).hi:ℝ) := hhhhi
      · have hbh' : (b.hi:ℝ) ≤ 0 := le_of_lt (lt_of_not_ge hbh)
        calc
          x*y ≤ x*(b.hi:ℝ) := mul_le_mul_of_nonneg_left hb.2 hx
          _ ≤ (a.lo:ℝ)*(b.hi:ℝ) := mul_le_mul_of_nonpos_right ha.1 hbh'
          _ ≤ ((mul a b).hi:ℝ) := hlhhi
    · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      by_cases hbl : 0 ≤ (b.lo:ℝ)
      · calc
          x*y ≤ x*(b.lo:ℝ) := mul_le_mul_of_nonpos_left hb.1 hx'
          _ ≤ (a.hi:ℝ)*(b.lo:ℝ) := mul_le_mul_of_nonneg_right ha.2 hbl
          _ ≤ ((mul a b).hi:ℝ) := hhlhi
      · have hbl' : (b.lo:ℝ) ≤ 0 := le_of_lt (lt_of_not_ge hbl)
        calc
          x*y ≤ x*(b.lo:ℝ) := mul_le_mul_of_nonpos_left hb.1 hx'
          _ ≤ (a.lo:ℝ)*(b.lo:ℝ) := mul_le_mul_of_nonpos_right ha.1 hbl'
          _ ≤ ((mul a b).hi:ℝ) := hllhi

/-- Exact reciprocal enclosure for positive pivots, now
interpreted as an interval containing a REAL reciprocal. -/
theorem inversePositive_containsReal
    {a : QInterval} {x : ℝ}
    (ha : ContainsReal a x) (hlo : 0 < a.lo) :
    ContainsReal (inversePositive a) x⁻¹ := by
  have hp : (0:ℝ) < (a.lo:ℝ) := by exact_mod_cast hlo
  have hx : 0 < x := lt_of_lt_of_le hp ha.1
  change (((a.hi)⁻¹ : ℚ) : ℝ) ≤ x⁻¹ ∧
    x⁻¹ ≤ (((a.lo)⁻¹ : ℚ) : ℝ)
  constructor
  · simpa only [Rat.cast_inv, one_div] using
      (one_div_le_one_div_of_le hx ha.2)
  · simpa only [Rat.cast_inv, one_div] using
      (one_div_le_one_div_of_le hp ha.1)

/-- Negative pivot reciprocals are obtained by signed
conjugation of the positive case. -/
theorem inverseNegative_containsReal
    {a : QInterval} {x : ℝ}
    (ha : ContainsReal a x) (hhi : a.hi < 0) :
    ContainsReal (inverseNegative a) x⁻¹ := by
  have hpos : 0 < (neg a).lo := by
    change 0 < -a.hi
    linarith
  have h := inversePositive_containsReal (neg_containsReal ha) hpos
  have hn := neg_containsReal h
  simpa only [inverseNegative, inv_neg, neg_neg] using hn

/-- Signed interval division sound for REAL values, with
all calculations using rational interval endpoints. -/
theorem inverseSigned_containsReal
    {a : QInterval} {x : ℝ}
    (ha : ContainsReal a x)
    (hsign : 0 < a.lo ∨ a.hi < 0) :
    ContainsReal (inverseSigned a) x⁻¹ := by
  by_cases hp : 0 < a.lo
  · simpa [inverseSigned, hp] using
      inversePositive_containsReal ha hp
  · have hn : a.hi < 0 := hsign.resolve_left hp
    simpa [inverseSigned, hp] using
      inverseNegative_containsReal ha hn

theorem divideSigned_containsReal
    {a b : QInterval} {x y : ℝ}
    (ha : ContainsReal a x) (hb : ContainsReal b y)
    (hsign : 0 < b.lo ∨ b.hi < 0) :
    ContainsReal (divideSigned a b) (x/y) := by
  simpa only [divideSigned, div_eq_mul_inv] using
    mul_containsReal ha (inverseSigned_containsReal hb hsign)

/-- The exact same Schur step in the rational checker bounds
the corresponding operation on REAL matrix coefficients. -/
theorem schurUpdate_containsReal
    {a_ij a_ik a_kj pivot : QInterval}
    {v_ij v_ik v_kj p : ℝ}
    (hij : ContainsReal a_ij v_ij)
    (hik : ContainsReal a_ik v_ik)
    (hkj : ContainsReal a_kj v_kj)
    (hp : ContainsReal pivot p)
    (hsign : 0 < pivot.lo ∨ pivot.hi < 0) :
    ContainsReal (schurUpdate a_ij a_ik a_kj pivot)
      (v_ij - v_ik*v_kj/p) := by
  exact sub_containsReal hij
    (divideSigned_containsReal (mul_containsReal hik hkj) hp hsign)

end W5.QInterval
