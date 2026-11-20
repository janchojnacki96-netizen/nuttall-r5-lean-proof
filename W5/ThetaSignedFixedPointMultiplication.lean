import W5.ThetaSignedFixedPointRounding
import W5.VerifiedIntervalRealSemantics
import W5.ThetaAudited768IntervalMatrices

/-!
# Verified signed four-corner multiplication at fixed 768-bit precision

The independent integer auditor computes the minimum and maximum of
the four signed endpoint products, then rounds the minimum DOWN and the
maximum UP with Euclidean integer division by D = 2^768.

This module implements that algorithm and proves that it encloses the
product of *real* inputs. It reuses:
* `fixedIntegerQuotient_rounds_outward` from the already CI-green PR 120;
* the Mathlib-supported rational/real four-corner multiplication theorem
  `QInterval.mul_containsReal`.

It does NOT implement transcendental exp, square roots, moment integrals,
or bound the actual analytic theta coefficients.
-/

namespace W5

/-- The smallest of all four signed endpoint products, before scaling. -/
def FixedIntInterval.productMin (a b : FixedIntInterval) : ℤ :=
  min (min (a.lo * b.lo) (a.lo * b.hi))
    (min (a.hi * b.lo) (a.hi * b.hi))

/-- The largest of all four signed endpoint products, before scaling. -/
def FixedIntInterval.productMax (a b : FixedIntInterval) : ℤ :=
  max (max (a.lo * b.lo) (a.lo * b.hi))
    (max (a.hi * b.lo) (a.hi * b.hi))

/-- The SAME scaled four-corner integer multiplication as the Python
auditor: floor(min/D), ceil(max/D), both for positive or negative values. -/
def FixedIntInterval.mul (a : FixedIntInterval) (D : ℤ)
    (b : FixedIntInterval) : FixedIntInterval :=
  ⟨(a.productMin b) / D, - ((-(a.productMax b)) / D)⟩

private theorem fixedMul_lower_corner
    (D u v m : ℤ) (hD : 0 < D) (hm : m ≤ u*v) :
    (((m / D : ℤ) : ℚ) / (D : ℚ)) ≤
      ((u : ℚ) / (D : ℚ)) * ((v : ℚ) / (D : ℚ)) := by
  have hDq : (0 : ℚ) ≤ (D : ℚ) := by exact_mod_cast (le_of_lt hD)
  have hfloor := (fixedIntegerQuotient_rounds_outward m D hD).1
  have hcast : (m : ℚ) ≤ (u : ℚ) * (v : ℚ) := by
    exact_mod_cast hm
  calc
    (((m / D : ℤ) : ℚ) / (D : ℚ)) ≤
        ((m : ℚ) / (D : ℚ)) / (D : ℚ) :=
      div_le_div_of_nonneg_right hfloor hDq
    _ ≤ (((u : ℚ) * (v : ℚ)) / (D : ℚ)) / (D : ℚ) := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hcast hDq) hDq
    _ = ((u : ℚ) / (D : ℚ)) * ((v : ℚ) / (D : ℚ)) := by
      ring

private theorem fixedMul_upper_corner
    (D u v m : ℤ) (hD : 0 < D) (hm : u*v ≤ m) :
    ((u : ℚ) / (D : ℚ)) * ((v : ℚ) / (D : ℚ)) ≤
      (((- ((-m) / D : ℤ) : ℤ) : ℚ) / (D : ℚ)) := by
  have hDq : (0 : ℚ) ≤ (D : ℚ) := by exact_mod_cast (le_of_lt hD)
  have hceil := (fixedIntegerQuotient_rounds_outward m D hD).2
  have hcast : (u : ℚ) * (v : ℚ) ≤ (m : ℚ) := by
    exact_mod_cast hm
  calc
    ((u : ℚ) / (D : ℚ)) * ((v : ℚ) / (D : ℚ)) =
        (((u : ℚ) * (v : ℚ)) / (D : ℚ)) / (D : ℚ) := by
      ring
    _ ≤ ((m : ℚ) / (D : ℚ)) / (D : ℚ) := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hcast hDq) hDq
    _ ≤ (((- ((-m) / D : ℤ) : ℤ) : ℚ) / (D : ℚ)) :=
      div_le_div_of_nonneg_right hceil hDq

/-- Integer-scaled outward multiplication encloses the pre-existing
EXACT rational four-corner interval product, at ANY positive scale. -/
theorem FixedIntInterval.mul_encloses_rational_mul
    (D : ℤ) (hD : 0 < D) (a b : FixedIntInterval) :
    ((a.mul D b).asQInterval D).lo ≤
      (QInterval.mul (a.asQInterval D) (b.asQInterval D)).lo ∧
    (QInterval.mul (a.asQInterval D) (b.asQInterval D)).hi ≤
      ((a.mul D b).asQInterval D).hi := by
  constructor
  · change (((a.productMin b / D : ℤ) : ℚ) / (D : ℚ)) ≤
      min
        (min (((a.lo : ℚ) / D) * ((b.lo : ℚ) / D))
             (((a.lo : ℚ) / D) * ((b.hi : ℚ) / D)))
        (min (((a.hi : ℚ) / D) * ((b.lo : ℚ) / D))
             (((a.hi : ℚ) / D) * ((b.hi : ℚ) / D)))
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · exact fixedMul_lower_corner D a.lo b.lo (a.productMin b) hD
        ((min_le_left _ _).trans (min_le_left _ _))
    · exact fixedMul_lower_corner D a.lo b.hi (a.productMin b) hD
        ((min_le_left _ _).trans (min_le_right _ _))
    · exact fixedMul_lower_corner D a.hi b.lo (a.productMin b) hD
        ((min_le_right _ _).trans (min_le_left _ _))
    · exact fixedMul_lower_corner D a.hi b.hi (a.productMin b) hD
        ((min_le_right _ _).trans (min_le_right _ _))
  · change
      max
        (max (((a.lo : ℚ) / D) * ((b.lo : ℚ) / D))
             (((a.lo : ℚ) / D) * ((b.hi : ℚ) / D)))
        (max (((a.hi : ℚ) / D) * ((b.lo : ℚ) / D))
             (((a.hi : ℚ) / D) * ((b.hi : ℚ) / D))) ≤
      (((- ((-(a.productMax b)) / D : ℤ) : ℤ) : ℚ) / (D : ℚ))
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · exact fixedMul_upper_corner D a.lo b.lo (a.productMax b) hD
        ((le_max_left _ _).trans (le_max_left _ _))
    · exact fixedMul_upper_corner D a.lo b.hi (a.productMax b) hD
        ((le_max_right _ _).trans (le_max_left _ _))
    · exact fixedMul_upper_corner D a.hi b.lo (a.productMax b) hD
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact fixedMul_upper_corner D a.hi b.hi (a.productMax b) hD
        ((le_max_right _ _).trans (le_max_right _ _))

/-- Fully sound multiplication for actual REAL inputs, even when
their intervals contain zero or have negative endpoints. -/
theorem FixedIntInterval.mul_containsReal
    (D : ℤ) (hD : 0 < D) (a b : FixedIntInterval)
    (x y : ℝ)
    (ha : QInterval.ContainsReal (a.asQInterval D) x)
    (hb : QInterval.ContainsReal (b.asQInterval D) y) :
    QInterval.ContainsReal ((a.mul D b).asQInterval D) (x*y) := by
  have hmul :=
    QInterval.mul_containsReal ha hb
  obtain ⟨hlo, hhi⟩ :=
    FixedIntInterval.mul_encloses_rational_mul D hD a b
  have hlow : (((a.mul D b).asQInterval D).lo : ℝ) ≤
      ((QInterval.mul (a.asQInterval D) (b.asQInterval D)).lo : ℝ) := by
    exact_mod_cast hlo
  have hhigh :
      ((QInterval.mul (a.asQInterval D) (b.asQInterval D)).hi : ℝ) ≤
      (((a.mul D b).asQInterval D).hi : ℝ) := by
    exact_mod_cast hhi
  exact ⟨hlow.trans hmul.1, hmul.2.trans hhigh⟩

/-- The exact integer scale and the large imported rational audit
data share precisely the same denominator. -/
theorem thetaAuditScale_eq_data_scale :
    (thetaAuditScale : ℚ) = thetaAuditScaleQ := by
  norm_num [thetaAuditScale, thetaAuditScaleQ]

/-- Specialize the full real soundness result to the actual 768-bit
scale, without duplicating the generic four-corner proof. -/
theorem FixedIntInterval.auditMul_containsReal
    (a b : FixedIntInterval) (x y : ℝ)
    (ha : QInterval.ContainsReal (a.asQInterval thetaAuditScale) x)
    (hb : QInterval.ContainsReal (b.asQInterval thetaAuditScale) y) :
    QInterval.ContainsReal
      ((a.mul thetaAuditScale b).asQInterval thetaAuditScale)
      (x*y) :=
  FixedIntInterval.mul_containsReal
    thetaAuditScale thetaAuditScale_pos a b x y ha hb

end W5
