import W5.ThetaBulkExponentialTaylor

/-!
# One rational exponential certificate for ALL Gamma w-bin boundaries

The exact finite Gamma mass formula needs exp(-L), exp(-U)
at many rational w-bin endpoints. Rather than introduce a new
transcendental oracle, reuse the existing Lean/Mathlib 65-term
Taylor exp certificate, its real-sound rational QInterval
evaluation and its 10 repeated-squaring lemma.

For 0 <= t <= 1024/3, let z = t/1024 <= 1/3. Then
  exp(-t) = (exp z)^(-1024).
Thus one rational interval operation (inversePositive)
followed by TEN squarings encloses exp(-t). Its only
side checks are decidable comparisons of rational endpoints.

This theorem applies at EVERY w-bin endpoint and every R5
x-cell, reducing a vast number of exponential evaluations to
one reusable proof. It is a candidate until Lean CI is green.
-/

namespace W5

/-- One computable exact-rational enclosure for exp(-t), where
t is a nonnegative rational argument. No floating-point inputs. -/
def thetaGammaBinExpNegBox (t : ℚ) : QInterval :=
  thetaBulkPow2 10
    (QInterval.inversePositive
      (thetaBulkExpTaylorBox
        (QInterval.point (t/1024))))

/-- A single verified real-semantic theorem for ALL nonnegative
rational Gamma integration endpoints up to 1024/3. -/
theorem thetaGammaBinExpNegBox_containsReal
    (t : ℚ)
    (ht : 0 ≤ t)
    (ht3 : t ≤ (1024:ℚ)/3)
    (hPos : 0 <
      (thetaBulkExpTaylorBox
        (QInterval.point (t/1024))).lo) :
    QInterval.ContainsReal
      (thetaGammaBinExpNegBox t)
      (Real.exp (-(t:ℝ))) := by
  let Z : QInterval := QInterval.point (t/1024)
  let z : ℝ := (t:ℝ)/1024
  have hp := thetaRationalPoint_containsReal (t/1024)
  have hz : QInterval.ContainsReal Z z := by
    simpa only [Z, z, Rat.cast_div, Rat.cast_ofNat] using hp
  have htR : (0:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have ht3R : (t:ℝ) ≤ (1024:ℝ)/3 := by
    have hc : (t:ℝ) ≤ (((1024:ℚ)/3):ℝ) := by
      exact_mod_cast ht3
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  have hz3 : z ≤ (1:ℝ)/3 := by
    dsimp [z]
    linarith
  have hExp : QInterval.ContainsReal
      (thetaBulkExpTaylorBox Z) (Real.exp z) :=
    thetaBulkExpTaylorBox_containsReal Z z hz hz0 hz3
  have hInv : QInterval.ContainsReal
      (QInterval.inversePositive (thetaBulkExpTaylorBox Z))
      (Real.exp z)⁻¹ :=
    QInterval.inversePositive_containsReal hExp hPos
  have hPower :=
    thetaBulkPow2_containsReal
      (QInterval.inversePositive (thetaBulkExpTaylorBox Z))
      (Real.exp z)⁻¹ hInv 10
  have hscale : (1024:ℝ)*z = (t:ℝ) := by
    dsimp [z]
    ring
  have hEpow :
      (Real.exp z)^1024 = Real.exp (t:ℝ) := by
    rw [← Real.exp_nat_mul]
    exact congrArg Real.exp hscale
  have hEq :
      (Real.exp z)⁻¹ ^ (2^10) =
        Real.exp (-(t:ℝ)) := by
    calc
      (Real.exp z)⁻¹ ^ (2^10) =
          ((Real.exp z)^1024)⁻¹ := by norm_num [inv_pow]
      _ = (Real.exp (t:ℝ))⁻¹ := by rw [hEpow]
      _ = Real.exp (-(t:ℝ)) := by
        rw [Real.exp_neg]
  simpa only [thetaGammaBinExpNegBox, Z, hEq] using hPower

end W5
