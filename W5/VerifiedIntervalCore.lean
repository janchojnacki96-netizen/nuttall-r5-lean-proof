import Mathlib

/-!
Small proved core for exact rational interval arithmetic.
All operations here use exact rational endpoints, not the integer
fixed-point rounding from the C++/Python certificate. The latter
remains an open formal verification obligation.
-/
namespace W5

structure QInterval where
  lo : ℚ
  hi : ℚ
deriving Repr, DecidableEq

namespace QInterval
def Contains (a : QInterval) (x : ℚ) : Prop :=
  a.lo ≤ x ∧ x ≤ a.hi

def add (a b : QInterval) : QInterval :=
  ⟨a.lo + b.lo, a.hi + b.hi⟩

def neg (a : QInterval) : QInterval :=
  ⟨-a.hi, -a.lo⟩

def sub (a b : QInterval) : QInterval :=
  add a (neg b)

def scaleNonneg (c : ℚ) (a : QInterval) : QInterval :=
  ⟨c * a.lo, c * a.hi⟩

theorem add_contains {a b : QInterval} {x y : ℚ}
    (ha : Contains a x) (hb : Contains b y) :
    Contains (add a b) (x + y) := by
  exact ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩

theorem neg_contains {a : QInterval} {x : ℚ}
    (ha : Contains a x) :
    Contains (neg a) (-x) := by
  exact ⟨neg_le_neg ha.2, neg_le_neg ha.1⟩

theorem sub_contains {a b : QInterval} {x y : ℚ}
    (ha : Contains a x) (hb : Contains b y) :
    Contains (sub a b) (x - y) := by
  simpa only [sub, sub_eq_add_neg] using
    add_contains ha (neg_contains hb)

theorem scaleNonneg_contains (c : ℚ) (hc : 0 ≤ c)
    {a : QInterval} {x : ℚ}
    (ha : Contains a x) :
    Contains (scaleNonneg c a) (c * x) := by
  exact ⟨mul_le_mul_of_nonneg_left ha.1 hc,
    mul_le_mul_of_nonneg_left ha.2 hc⟩

end QInterval
end W5
