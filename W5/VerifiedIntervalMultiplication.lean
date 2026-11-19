import W5.VerifiedIntervalCore

/-!
Soundness of the exact four-corner interval product, over rational numbers.
Unlike naive endpoint multiplication, this handles signed intervals.
Integer fixed-point rounding from the original certificate is a distinct
unproved obligation.
-/

namespace W5.QInterval

def mul (a b : QInterval) : QInterval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi))
       (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi))
       (max (a.hi*b.lo) (a.hi*b.hi))⟩

private theorem lo_le_ll (a b : QInterval) :
    (mul a b).lo ≤ a.lo*b.lo := by
  exact le_trans (min_le_left _ _) (min_le_left _ _)

private theorem lo_le_lh (a b : QInterval) :
    (mul a b).lo ≤ a.lo*b.hi := by
  exact le_trans (min_le_left _ _) (min_le_right _ _)

private theorem lo_le_hl (a b : QInterval) :
    (mul a b).lo ≤ a.hi*b.lo := by
  exact le_trans (min_le_right _ _) (min_le_left _ _)

private theorem lo_le_hh (a b : QInterval) :
    (mul a b).lo ≤ a.hi*b.hi := by
  exact le_trans (min_le_right _ _) (min_le_right _ _)

private theorem ll_le_hi (a b : QInterval) :
    a.lo*b.lo ≤ (mul a b).hi := by
  exact le_trans (le_max_left _ _) (le_max_left _ _)

private theorem lh_le_hi (a b : QInterval) :
    a.lo*b.hi ≤ (mul a b).hi := by
  exact le_trans (le_max_right _ _) (le_max_left _ _)

private theorem hl_le_hi (a b : QInterval) :
    a.hi*b.lo ≤ (mul a b).hi := by
  exact le_trans (le_max_left _ _) (le_max_right _ _)

private theorem hh_le_hi (a b : QInterval) :
    a.hi*b.hi ≤ (mul a b).hi := by
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem mul_contains {a b : QInterval} {x y : ℚ}
    (ha : Contains a x) (hb : Contains b y) :
    Contains (mul a b) (x*y) := by
  change (mul a b).lo ≤ x*y ∧ x*y ≤ (mul a b).hi
  constructor
  · by_cases hx : 0 ≤ x
    · by_cases hbl : 0 ≤ b.lo
      · calc
          (mul a b).lo ≤ a.lo*b.lo := lo_le_ll a b
          _ ≤ x*b.lo := mul_le_mul_of_nonneg_right ha.1 hbl
          _ ≤ x*y := mul_le_mul_of_nonneg_left hb.1 hx
      · have hbl' : b.lo ≤ 0 := le_of_lt (lt_of_not_ge hbl)
        calc
          (mul a b).lo ≤ a.hi*b.lo := lo_le_hl a b
          _ ≤ x*b.lo := mul_le_mul_of_nonpos_right ha.2 hbl'
          _ ≤ x*y := mul_le_mul_of_nonneg_left hb.1 hx
    · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      by_cases hbh : 0 ≤ b.hi
      · calc
          (mul a b).lo ≤ a.lo*b.hi := lo_le_lh a b
          _ ≤ x*b.hi := mul_le_mul_of_nonneg_right ha.1 hbh
          _ ≤ x*y := mul_le_mul_of_nonpos_left hb.2 hx'
      · have hbh' : b.hi ≤ 0 := le_of_lt (lt_of_not_ge hbh)
        calc
          (mul a b).lo ≤ a.hi*b.hi := lo_le_hh a b
          _ ≤ x*b.hi := mul_le_mul_of_nonpos_right ha.2 hbh'
          _ ≤ x*y := mul_le_mul_of_nonpos_left hb.2 hx'
  · by_cases hx : 0 ≤ x
    · by_cases hbh : 0 ≤ b.hi
      · calc
          x*y ≤ x*b.hi := mul_le_mul_of_nonneg_left hb.2 hx
          _ ≤ a.hi*b.hi := mul_le_mul_of_nonneg_right ha.2 hbh
          _ ≤ (mul a b).hi := hh_le_hi a b
      · have hbh' : b.hi ≤ 0 := le_of_lt (lt_of_not_ge hbh)
        calc
          x*y ≤ x*b.hi := mul_le_mul_of_nonneg_left hb.2 hx
          _ ≤ a.lo*b.hi := mul_le_mul_of_nonpos_right ha.1 hbh'
          _ ≤ (mul a b).hi := lh_le_hi a b
    · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      by_cases hbl : 0 ≤ b.lo
      · calc
          x*y ≤ x*b.lo := mul_le_mul_of_nonpos_left hb.1 hx'
          _ ≤ a.hi*b.lo := mul_le_mul_of_nonneg_right ha.2 hbl
          _ ≤ (mul a b).hi := hl_le_hi a b
      · have hbl' : b.lo ≤ 0 := le_of_lt (lt_of_not_ge hbl)
        calc
          x*y ≤ x*b.lo := mul_le_mul_of_nonpos_left hb.1 hx'
          _ ≤ a.lo*b.lo := mul_le_mul_of_nonpos_right ha.1 hbl'
          _ ≤ (mul a b).hi := ll_le_hi a b

end W5.QInterval
