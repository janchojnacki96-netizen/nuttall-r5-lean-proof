import W5.ThetaBulkExponentialTaylor
import W5.ThetaSignedFixedPointMultiplication
import Mathlib.Data.Rat.Floor

/-!
# Efficient 768-bit certified Gaussian exp for EVERY theta x-cell

The exact rational exp(z) Taylor box from #150 is small.
Computing (1/exp(z))^1024 as a raw rational grows enormous
numerators/denominators; the whole 48-cell LDL sweep would be slow.

Reuse W5's ALREADY PROVED outward 768-bit signed integer
multiplication and Mathlib's exact rational floor/ceil:
1. Round the rational exp(z) reciprocal outward to scale 2^768.
2. Square the integer interval ten times, rounding each
   multiplication outward (the actual Python auditor algorithm).
3. Reuse real soundness to retain exp(-(n²-1)/x²).

This bounds numerical complexity to TEN integer multiplications
on small fixed-point intervals per (x-cell,n), rather than
multiplying million-bit rational denominators. No floating point.
-/

namespace W5

/-- Compress any exact rational interval to the SAME 768-bit
integer scale as the already certified auditor. Both rounding
directions use Mathlib's executable floor/ceil on rationals. -/
def thetaBulkRoundToAuditScale (I : QInterval) : FixedIntInterval :=
  ⟨⌊I.lo * (thetaAuditScale:ℚ)⌋,
   ⌈I.hi * (thetaAuditScale:ℚ)⌉⟩

/-- Outward rounding of an arbitrary rational interval preserves
containment of a genuine REAL value. -/
theorem thetaBulkRoundToAuditScale_containsReal
    (I : QInterval) (x : ℝ)
    (hx : QInterval.ContainsReal I x) :
    QInterval.ContainsReal
      ((thetaBulkRoundToAuditScale I).asQInterval thetaAuditScale)
      x := by
  have hDq : (0:ℚ) < (thetaAuditScale:ℚ) := by
    exact_mod_cast thetaAuditScale_pos
  have hlo :
      ((⌊I.lo*(thetaAuditScale:ℚ)⌋ : ℤ) : ℚ) ≤
        I.lo*(thetaAuditScale:ℚ) := Int.floor_le _
  have hhi :
      I.hi*(thetaAuditScale:ℚ) ≤
        ((⌈I.hi*(thetaAuditScale:ℚ)⌉ : ℤ) : ℚ) := Int.le_ceil _
  have hloq :
      (((⌊I.lo*(thetaAuditScale:ℚ)⌋ : ℤ):ℚ) /
        (thetaAuditScale:ℚ)) ≤ I.lo :=
    (div_le_iff₀ hDq).2 hlo
  have hhiq : I.hi ≤
      (((⌈I.hi*(thetaAuditScale:ℚ)⌉ : ℤ):ℚ) /
        (thetaAuditScale:ℚ)) :=
    (le_div_iff₀ hDq).2 hhi
  have hloR :
      ((((⌊I.lo*(thetaAuditScale:ℚ)⌋ : ℤ):ℚ) /
        (thetaAuditScale:ℚ)):ℝ) ≤ (I.lo:ℝ) := by
    exact_mod_cast hloq
  have hhiR : (I.hi:ℝ) ≤
      ((((⌈I.hi*(thetaAuditScale:ℚ)⌉ : ℤ):ℚ) /
        (thetaAuditScale:ℚ)):ℝ) := by
    exact_mod_cast hhiq
  change
    ((((⌊I.lo*(thetaAuditScale:ℚ)⌋ : ℤ):ℚ) /
      (thetaAuditScale:ℚ)):ℝ) ≤ x ∧
    x ≤ ((((⌈I.hi*(thetaAuditScale:ℚ)⌉ : ℤ):ℚ) /
      (thetaAuditScale:ℚ)):ℝ)
  exact ⟨hloR.trans hx.1, hx.2.trans hhiR⟩

/-- Repeated certified 768-bit SQUARING. One generic soundness
induction covers any depth, and the original exponential
needs depth 10. -/
def thetaBulkFixedPow2 : ℕ → FixedIntInterval → FixedIntInterval
  | 0, I => I
  | k+1, I =>
      let J := thetaBulkFixedPow2 k I
      J.mul thetaAuditScale J

theorem thetaBulkFixedPow2_containsReal
    (I : FixedIntInterval) (x : ℝ)
    (hx : QInterval.ContainsReal
      (I.asQInterval thetaAuditScale) x) :
    ∀ k : ℕ,
      QInterval.ContainsReal
        ((thetaBulkFixedPow2 k I).asQInterval thetaAuditScale)
        (x^(2^k)) := by
  intro k
  induction k with
  | zero =>
      simpa only [thetaBulkFixedPow2, pow_zero, pow_one] using hx
  | succ k ih =>
      have hMul := FixedIntInterval.auditMul_containsReal
        (thetaBulkFixedPow2 k I) (thetaBulkFixedPow2 k I)
        (x^(2^k)) (x^(2^k)) ih ih
      have hpow : x^(2^(k+1)) = x^(2^k)*x^(2^k) := by
        rw [pow_succ, pow_mul, pow_two]
      simpa only [thetaBulkFixedPow2, hpow] using hMul

/-- SAME exact-R5 exponential enclosure, but all ten squarings
are rounded outward to 768 bits, preventing denominator explosion. -/
def thetaBulkFixedGaussianExpBox (a b : ℚ) (n : ℕ) : QInterval :=
  ((thetaBulkFixedPow2 10
    (thetaBulkRoundToAuditScale
      (QInterval.inversePositive
        (thetaBulkExpTaylorBox (thetaBulkReducedExpArgBox a b n))))).
    asQInterval thetaAuditScale)

/-- The compact 768-bit Gaussian enclosure still contains the
true original exp(-(n²-1)/x²), with precisely the same two
rational preconditions as the unreduced #150 variant. -/
theorem thetaBulkFixedGaussianExpBox_containsReal
    (a b : ℚ) (x : ℝ) (n : ℕ)
    (ha : (0:ℚ) < a)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hn : 2 ≤ n)
    (hRange : (thetaBulkReducedExpArgBox a b n).hi ≤ (1:ℚ)/3)
    (hPos : 0 <
      (thetaBulkExpTaylorBox (thetaBulkReducedExpArgBox a b n)).lo) :
    QInterval.ContainsReal (thetaBulkFixedGaussianExpBox a b n)
      (Real.exp (-((n:ℝ)^2-1)/x^2)) := by
  let Z := thetaBulkReducedExpArgBox a b n
  let z : ℝ := ((n:ℝ)^2-1)/(1024*x^2)
  have hz : QInterval.ContainsReal Z z :=
    thetaBulkReducedExpArgBox_containsReal a b x n ha hax hxb hn
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hx : 0 < x := haR.trans_le hax
  have hN : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg (by nlinarith)
      (mul_nonneg (by norm_num) (sq_nonneg x))
  have hz3 : z ≤ (1:ℝ)/3 := by
    have hQ : ((thetaBulkReducedExpArgBox a b n).hi:ℝ) ≤
        (1:ℝ)/3 := by exact_mod_cast hRange
    exact hz.2.trans hQ
  have hExp := thetaBulkExpTaylorBox_containsReal Z z hz hz0 hz3
  have hInv :=
    QInterval.inversePositive_containsReal hExp hPos
  have hSnap :=
    thetaBulkRoundToAuditScale_containsReal
      (QInterval.inversePositive (thetaBulkExpTaylorBox Z))
      (Real.exp z)⁻¹ hInv
  have hPower := thetaBulkFixedPow2_containsReal
    (thetaBulkRoundToAuditScale
      (QInterval.inversePositive (thetaBulkExpTaylorBox Z)))
    (Real.exp z)⁻¹ hSnap 10
  have hscale : (1024:ℝ)*z = ((n:ℝ)^2-1)/x^2 := by
    dsimp [z]
    have hx2 : x^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hx)
    field_simp [hx2]
    ring
  have hEpow :
      (Real.exp z)^1024 =
        Real.exp (((n:ℝ)^2-1)/x^2) := by
    rw [← Real.exp_nat_mul, hscale]
  have hEq : (Real.exp z)⁻¹ ^ (2^10) =
      Real.exp (-((n:ℝ)^2-1)/x^2) := by
    calc
      (Real.exp z)⁻¹ ^ (2^10) =
          ((Real.exp z)^1024)⁻¹ := by norm_num [inv_pow]
      _ = (Real.exp (((n:ℝ)^2-1)/x^2))⁻¹ := by rw [hEpow]
      _ = Real.exp (-((n:ℝ)^2-1)/x^2) := by
        rw [Real.exp_neg, neg_div]
  simpa only [thetaBulkFixedGaussianExpBox, Z, hEq] using hPower

end W5
