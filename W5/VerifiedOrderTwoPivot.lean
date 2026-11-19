import W5.VerifiedIntervalDivision

/-!
# Sound exact-rational LDL second pivot bound

This module gives an executable rational interval enclosure for the
second LDL pivot of a symmetric two-by-two matrix. It uses the
proved four-corner multiplication, subtraction and signed division
primitives. The certified negative second-pivot enclosure implies
the exact negative determinant, provided the first pivot is positive.

These are genuine algebraic and interval-soundness results. Connecting
the input intervals to the analytic theta coefficients is still open.
-/

namespace W5.QInterval

/-- Enclose `a11 - a01²/a00`, the second LDL pivot. This
operator is sound when the input interval `a00` is positive. -/
def secondPivot (a00 a01 a11 : QInterval) : QInterval :=
  sub a11 (divPositive (mul a01 a01) a00)

/-- Every exact second Schur pivot lies in the computed interval. -/
theorem secondPivot_contains
    {a00 a01 a11 : QInterval} {x00 x01 x11 : ℚ}
    (h00 : Contains a00 x00)
    (h01 : Contains a01 x01)
    (h11 : Contains a11 x11)
    (hpositive : 0 < a00.lo) :
    Contains (secondPivot a00 a01 a11)
      (x11 - x01 * x01 / x00) := by
  have hprod : Contains (mul a01 a01) (x01 * x01) :=
    mul_contains h01 h01
  have hdiv : Contains (divPositive (mul a01 a01) a00)
      ((x01 * x01) / x00) :=
    divPositive_contains hprod h00 hpositive
  simpa only [secondPivot] using sub_contains h11 hdiv

/-- A strictly negative upper enclosure certifies the sign of the
exact second pivot. -/
theorem secondPivot_negative_of_upper
    {a00 a01 a11 : QInterval} {x00 x01 x11 : ℚ}
    (h00 : Contains a00 x00)
    (h01 : Contains a01 x01)
    (h11 : Contains a11 x11)
    (hpositive : 0 < a00.lo)
    (hupper : (secondPivot a00 a01 a11).hi < 0) :
    x11 - x01 * x01 / x00 < 0 :=
  lt_of_le_of_lt
    (secondPivot_contains h00 h01 h11 hpositive).2 hupper

/-- Sound interval LDL sign test for the genuine 2x2 determinant.
It makes no assertion about which intervals enclose theta entries. -/
theorem determinant_two_negative_of_secondPivot_upper
    {a00 a01 a11 : QInterval} {x00 x01 x11 : ℚ}
    (h00 : Contains a00 x00)
    (h01 : Contains a01 x01)
    (h11 : Contains a11 x11)
    (hpositive : 0 < a00.lo)
    (hupper : (secondPivot a00 a01 a11).hi < 0) :
    x00 * x11 - x01 * x01 < 0 := by
  have hx00 : 0 < x00 := lt_of_lt_of_le hpositive h00.1
  have hp : x11 - x01 * x01 / x00 < 0 :=
    secondPivot_negative_of_upper h00 h01 h11 hpositive hupper
  have hmul : x00 * (x01 * x01 / x00) = x01 * x01 := by
    field_simp [ne_of_gt hx00] <;> ring
  have hneg : x00 * (x11 - x01 * x01 / x00) < 0 :=
    mul_neg_of_pos_of_neg hx00 hp
  nlinarith

end W5.QInterval
