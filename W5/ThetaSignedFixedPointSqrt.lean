import W5.ThetaSignedFixedPointMultiplication
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Real.Sqrt

/-!
# Sound integer square-root rounding for the original 768-bit auditor

The Python integer auditor computes integer square roots of the scaled
products a*D, with lower endpoint floor(isqrt) and upper endpoint the
ceil of the exact square root, only increasing it when the radicand
is not a perfect integer square.

We reuse Mathlib's already proved Nat.sqrt_le' and
Nat.lt_succ_sqrt' to derive the two integer square inequalities.
We then use Real.sq_sqrt and Real.sqrt_le_sqrt to prove containment
of the genuine REAL square root.

No separate square-root algorithm or untrusted floating arithmetic
is introduced. This verifies the fixed-scale rounding operator
only: its use on the original theta weighted moments still requires
the analytic moment enclosures.
-/

namespace W5

/-- Mathlib's integer square root, applied to a nonnegative scaled
radicand. Negative integers are mapped to zero by Int.toNat;
soundness will always require a ≥ 0 and D > 0. -/
def fixedPointSqrtFloor (a D : ℤ) : ℤ :=
  (Nat.sqrt ((a*D).toNat) : ℤ)

/-- Exact ceil of the integer square root, equal to its floor
when a*D is a perfect square and floor+1 otherwise. -/
def fixedPointSqrtCeil (a D : ℤ) : ℤ :=
  if (fixedPointSqrtFloor a D)^2 = a*D then
    fixedPointSqrtFloor a D
  else fixedPointSqrtFloor a D + 1

/-- The lower integer square root always underestimates the true
scaled radicand; use the existing Mathlib isqrt certificate. -/
theorem fixedPointSqrtFloor_square_le
    (a D : ℤ) (ha : 0 ≤ a) (hD : 0 < D) :
    (fixedPointSqrtFloor a D)^2 ≤ a*D := by
  have hz : 0 ≤ a*D := mul_nonneg ha (le_of_lt hD)
  have h := Nat.sqrt_le' ((a*D).toNat)
  have hcast : ((Nat.sqrt ((a*D).toNat) : ℤ)^2) ≤
      ((a*D).toNat : ℤ) := by
    exact_mod_cast h
  simpa only [fixedPointSqrtFloor, Int.toNat_of_nonneg hz] using hcast

/-- The next integer after the floor has square strictly larger
than the true scaled radicand, again from a Mathlib lemma. -/
theorem fixedPointSqrtFloor_lt_succ_square
    (a D : ℤ) (ha : 0 ≤ a) (hD : 0 < D) :
    a*D < (fixedPointSqrtFloor a D + 1)^2 := by
  have hz : 0 ≤ a*D := mul_nonneg ha (le_of_lt hD)
  have h := Nat.lt_succ_sqrt' ((a*D).toNat)
  have hcast : ((a*D).toNat : ℤ) <
      ((Nat.sqrt ((a*D).toNat) : ℤ) + 1)^2 := by
    exact_mod_cast h
  simpa only [fixedPointSqrtFloor, Int.toNat_of_nonneg hz] using hcast

theorem fixedPointSqrtFloor_nonneg (a D : ℤ) :
    0 ≤ fixedPointSqrtFloor a D := by
  unfold fixedPointSqrtFloor
  exact Int.natCast_nonneg _

theorem fixedPointSqrtCeil_nonneg (a D : ℤ) :
    0 ≤ fixedPointSqrtCeil a D := by
  unfold fixedPointSqrtCeil
  split_ifs
  · exact fixedPointSqrtFloor_nonneg a D
  · have h := fixedPointSqrtFloor_nonneg a D
    omega

/-- Ceil (isqrt) is an outward integer enclosure even when
the scaled radicand is a perfect square. -/
theorem fixedPointSqrtCeil_square_ge
    (a D : ℤ) (ha : 0 ≤ a) (hD : 0 < D) :
    a*D ≤ (fixedPointSqrtCeil a D)^2 := by
  unfold fixedPointSqrtCeil
  split_ifs with h
  · exact h.symm.le
  · exact (fixedPointSqrtFloor_lt_succ_square a D ha hD).le

/-- Mathlib square-root monotonicity in a purely ordered-real form.
This avoids any custom analytic argument for sqrt. -/
private theorem realSqrt_between_squares (t l u : ℝ)
    (ht : 0 ≤ t) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlsq : l^2 ≤ t) (husq : t ≤ u^2) :
    l ≤ Real.sqrt t ∧ Real.sqrt t ≤ u := by
  have hs := Real.sq_sqrt ht
  have hr := Real.sqrt_nonneg t
  constructor <;> nlinarith

/-- Exact integer sqrt rounding bounds the TRUE real sqrt of
the corresponding positive fixed-point rational number. -/
theorem fixedPointSqrt_rounds_real
    (a D : ℤ) (ha : 0 ≤ a) (hD : 0 < D) :
    ((fixedPointSqrtFloor a D : ℝ) / (D : ℝ)) ≤
        Real.sqrt ((a : ℝ) / (D : ℝ)) ∧
      Real.sqrt ((a : ℝ) / (D : ℝ)) ≤
        ((fixedPointSqrtCeil a D : ℝ) / (D : ℝ)) := by
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have har : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hloSq : ((fixedPointSqrtFloor a D : ℝ)^2) ≤
      (a : ℝ) * (D : ℝ) := by
    exact_mod_cast fixedPointSqrtFloor_square_le a D ha hD
  have hhiSq : (a : ℝ) * (D : ℝ) ≤
      (fixedPointSqrtCeil a D : ℝ)^2 := by
    exact_mod_cast fixedPointSqrtCeil_square_ge a D ha hD
  have hd2 : (0 : ℝ) ≤ (D : ℝ)^2 := by positivity
  have hlow :
      ((fixedPointSqrtFloor a D : ℝ) / (D : ℝ))^2 ≤
        (a : ℝ) / (D : ℝ) := by
    calc
      ((fixedPointSqrtFloor a D : ℝ) / (D : ℝ))^2 =
        ((fixedPointSqrtFloor a D : ℝ)^2) / ((D : ℝ)^2) := by ring
      _ ≤ ((a : ℝ) * (D : ℝ)) / ((D : ℝ)^2) :=
        div_le_div_of_nonneg_right hloSq hd2
      _ = (a : ℝ) / (D : ℝ) := by
        field_simp [ne_of_gt hDr]
  have hhigh :
      (a : ℝ) / (D : ℝ) ≤
        ((fixedPointSqrtCeil a D : ℝ) / (D : ℝ))^2 := by
    calc
      (a : ℝ) / (D : ℝ) =
        ((a : ℝ) * (D : ℝ)) / ((D : ℝ)^2) := by
        field_simp [ne_of_gt hDr]
      _ ≤ ((fixedPointSqrtCeil a D : ℝ)^2) / ((D : ℝ)^2) :=
        div_le_div_of_nonneg_right hhiSq hd2
      _ = ((fixedPointSqrtCeil a D : ℝ) / (D : ℝ))^2 := by ring
  exact realSqrt_between_squares
    ((a : ℝ) / (D : ℝ))
    ((fixedPointSqrtFloor a D : ℝ) / (D : ℝ))
    ((fixedPointSqrtCeil a D : ℝ) / (D : ℝ))
    (div_nonneg har hDr.le)
    (div_nonneg (by exact_mod_cast fixedPointSqrtFloor_nonneg a D) hDr.le)
    (div_nonneg (by exact_mod_cast fixedPointSqrtCeil_nonneg a D) hDr.le)
    hlow hhigh

/-- The exact fixed-point interval sqrt used in the auditor. -/
def FixedIntInterval.sqrt (a : FixedIntInterval) (D : ℤ) :
    FixedIntInterval :=
  ⟨fixedPointSqrtFloor a.lo D, fixedPointSqrtCeil a.hi D⟩

/-- Real soundness of the sqrt interval at arbitrary positive integer
scale. Both the lower and upper input endpoints must be nonnegative,
as in the original Python assertion. -/
theorem FixedIntInterval.sqrt_containsReal
    (D : ℤ) (hD : 0 < D) (a : FixedIntInterval)
    (hlo : 0 ≤ a.lo) (hhi : 0 ≤ a.hi) (x : ℝ)
    (hx : QInterval.ContainsReal (a.asQInterval D) x) :
    QInterval.ContainsReal
      ((a.sqrt D).asQInterval D) (Real.sqrt x) := by
  have hlow := (fixedPointSqrt_rounds_real a.lo D hlo hD).1
  have hhigh := (fixedPointSqrt_rounds_real a.hi D hhi hD).2
  have hx' : ((a.lo : ℝ) / (D : ℝ) ≤ x) ∧
      (x ≤ (a.hi : ℝ) / (D : ℝ)) := by
    simpa only [QInterval.ContainsReal, FixedIntInterval.asQInterval,
      Rat.cast_div, Rat.cast_intCast] using hx
  have hbounds :
      (fixedPointSqrtFloor a.lo D : ℝ) / (D : ℝ) ≤ Real.sqrt x ∧
        Real.sqrt x ≤ (fixedPointSqrtCeil a.hi D : ℝ) / (D : ℝ) :=
    ⟨hlow.trans (Real.sqrt_le_sqrt hx'.1),
      (Real.sqrt_le_sqrt hx'.2).trans hhigh⟩
  simpa only [QInterval.ContainsReal, FixedIntInterval.asQInterval,
    FixedIntInterval.sqrt, Rat.cast_div, Rat.cast_intCast] using hbounds

/-- The actual 768-bit sqrt, sharing its scale with the auditor. -/
theorem FixedIntInterval.auditSqrt_containsReal
    (a : FixedIntInterval) (hlo : 0 ≤ a.lo) (hhi : 0 ≤ a.hi)
    (x : ℝ)
    (hx : QInterval.ContainsReal
      (a.asQInterval thetaAuditScale) x) :
    QInterval.ContainsReal
      ((a.sqrt thetaAuditScale).asQInterval thetaAuditScale)
      (Real.sqrt x) :=
  FixedIntInterval.sqrt_containsReal thetaAuditScale thetaAuditScale_pos
    a hlo hhi x hx

end W5
