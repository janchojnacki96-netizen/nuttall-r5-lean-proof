import Nuttall.CompactFixedCongruence

namespace Nuttall

open W5

/-- Divide both endpoints by a positive integer, rounding outward. -/
def compactFixedDiv (J : FixedIntInterval) (q : ℤ) : FixedIntInterval :=
  ⟨J.lo / q, -((-J.hi) / q)⟩

theorem compactFixedDiv_containsReal {D q : ℤ} (hD : 0 < D) (hq : 0 < q)
    {J : FixedIntInterval} {x : ℝ} (hx : (J.asQInterval D).ContainsReal x) :
    ((compactFixedDiv J q).asQInterval D).ContainsReal (x / (q:ℝ)) := by
  have hDr : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hlo : ((J.lo / q : ℤ):ℝ) ≤ (J.lo:ℝ)/(q:ℝ) := by
    exact_mod_cast (fixedIntegerQuotient_rounds_outward J.lo q hq).1
  have hhi : (J.hi:ℝ)/(q:ℝ) ≤ ((-((-J.hi)/q) : ℤ):ℝ) := by
    exact_mod_cast (fixedIntegerQuotient_rounds_outward J.hi q hq).2
  simp only [QInterval.ContainsReal, FixedIntInterval.asQInterval,
    Rat.cast_div, Rat.cast_intCast] at hx
  constructor
  · simp only [compactFixedDiv, FixedIntInterval.asQInterval, Rat.cast_div, Rat.cast_intCast]
    calc
      _ ≤ ((J.lo:ℝ)/(q:ℝ))/(D:ℝ) := div_le_div_of_nonneg_right hlo hDr.le
      _ = ((J.lo:ℝ)/(D:ℝ))/(q:ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hx.1 hqr.le
  · simp only [compactFixedDiv, FixedIntInterval.asQInterval, Rat.cast_div, Rat.cast_intCast]
    calc
      _ ≤ ((J.hi:ℝ)/(D:ℝ))/(q:ℝ) := div_le_div_of_nonneg_right hx.2 hqr.le
      _ = ((J.hi:ℝ)/(q:ℝ))/(D:ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hhi hDr.le

/-- Scale a Hankel derivative and its Taylor monomial using one integer division. -/
def compactDyadicCoefficient (radiusBits l k : ℕ) (J : FixedIntInterval) : FixedIntInterval :=
  compactFixedDiv J (16^l * (2^radiusBits)^k * (k.factorial:ℤ))

theorem compactDyadicCoefficient_containsReal {D : ℤ} (hD : 0 < D)
    {J : FixedIntInterval} {x : ℝ} (hx : (J.asQInterval D).ContainsReal x)
    (radiusBits l k : ℕ) :
    ((compactDyadicCoefficient radiusBits l k J).asQInterval D).ContainsReal
      ((1/16:ℝ)^l * (1/(2:ℝ)^radiusBits)^k / (k.factorial:ℝ) * x) := by
  have hz : 0 < (16:ℤ)^l * (2^radiusBits)^k * (k.factorial:ℤ) := by positivity
  unfold compactDyadicCoefficient
  convert compactFixedDiv_containsReal hD hz hx using 1
  push_cast
  simp only [div_pow, one_pow]
  ring

#print axioms compactDyadicCoefficient_containsReal

end Nuttall
