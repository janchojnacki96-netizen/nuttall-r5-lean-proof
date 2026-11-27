import Nuttall.OriginWronskianInterval
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Rat.Floor

namespace Nuttall

open W5
open scoped BigOperators

private def expNegTaylor (z : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 16, (-z/16)^k / (k.factorial:ℚ)

private theorem expNegTaylor_abs (z : ℚ) (hz₀ : 0 ≤ z) (hz₁ : z ≤ 16) :
    |Real.exp (-(z:ℝ)/16) - (expNegTaylor z : ℝ)| ≤ (1:ℝ)/10^12 := by
  have hzR₀ : (0:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz₀
  have hzR₁ : (z:ℝ) ≤ 16 := by exact_mod_cast hz₁
  have hx : |-(z:ℝ)/16| ≤ 1 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have he := Real.exp_bound (n := 16) hx (by decide)
  have hc : ((expNegTaylor z : ℚ):ℝ) =
      ∑ k ∈ Finset.range 16, (-(z:ℝ)/16)^k / (k.factorial:ℝ) := by
    simp only [expNegTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_neg, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_natCast]
  rw [hc]
  refine he.trans ?_
  calc
    _ ≤ (1:ℝ)^16 * ((16:ℝ)+1) / ((Nat.factorial 16:ℝ)*16) := by
      have hb := pow_le_pow_left₀ (abs_nonneg _) hx 16
      norm_num only [Nat.cast_ofNat] at *
      gcongr
    _ ≤ _ := by norm_num [Nat.factorial]

private def phiCompactExpLo (z : ℚ) : ℚ :=
  max 0 (expNegTaylor z - 1/10^12)

private def phiCompactExpHi (z : ℚ) : ℚ :=
  expNegTaylor z + 1/10^12

private theorem phiCompactExpScaled_bounds (z : ℚ) (hz₀ : 0 ≤ z) (hz₁ : z ≤ 16) :
    ((phiCompactExpLo z:ℚ):ℝ) ≤ Real.exp (-(z:ℝ)/16) ∧
      Real.exp (-(z:ℝ)/16) ≤ ((phiCompactExpHi z:ℚ):ℝ) := by
  have h := abs_le.mp (expNegTaylor_abs z hz₀ hz₁)
  constructor
  · unfold phiCompactExpLo
    have hcast : ((max 0 (expNegTaylor z - 1/10^12) : ℚ):ℝ) =
        max 0 ((expNegTaylor z:ℝ)-1/10^12) := by
      rw [Rat.cast_mono.map_max]
      push_cast <;> rfl
    rw [hcast]
    exact max_le (Real.exp_pos _).le (by linarith only [h.1])
  · unfold phiCompactExpHi
    push_cast
    linarith only [h.2]

private def expRoundDown (q : ℚ) : ℚ := (⌊q * 10^22⌋ : ℤ) / (10:ℚ)^22
private def expRoundUp (q : ℚ) : ℚ := (⌈q * 10^22⌉ : ℤ) / (10:ℚ)^22

/-- Endpoints for exp(-X) over a rational X-cell. Rounding outward before taking the
square-index powers keeps denominators bounded in the finite determinant check. -/
def phiCompactExpBox (a b : ℚ) : QInterval :=
  ⟨expRoundDown ((phiCompactExpLo b)^16), expRoundUp ((phiCompactExpHi a)^16)⟩

theorem phiCompactExpBox_containsReal {a b : ℚ} {X : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 16) (hlo : (a:ℝ) ≤ X) (hhi : X ≤ (b:ℝ)) :
    (phiCompactExpBox a b).ContainsReal (Real.exp (-X)) := by
  have hab : a ≤ b := by exact_mod_cast hlo.trans hhi
  have hA := phiCompactExpScaled_bounds a ha (hab.trans hb)
  have hB := phiCompactExpScaled_bounds b (ha.trans hab) hb
  have hL : (0:ℝ) ≤ (phiCompactExpLo b : ℝ) := by
    exact_mod_cast (show 0 ≤ phiCompactExpLo b from le_max_left _ _)
  have hBpow := pow_le_pow_left₀ hL hB.1 16
  have hApow := pow_le_pow_left₀ (Real.exp_pos _).le hA.2 16
  have hpower (v : ℝ) : Real.exp (-v/16)^16 = Real.exp (-v) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hpower] at hBpow hApow
  have hroundL (q : ℚ) : expRoundDown q ≤ q := by
    exact (div_le_iff₀ (by norm_num)).2 (Int.floor_le _)
  have hroundU (q : ℚ) : q ≤ expRoundUp q := by
    exact (le_div_iff₀ (by norm_num)).2 (Int.le_ceil _)
  have hL₀ : ((expRoundDown ((phiCompactExpLo b)^16) : ℚ):ℝ) ≤
      ((phiCompactExpLo b:ℚ):ℝ)^16 := by
    exact_mod_cast hroundL ((phiCompactExpLo b)^16)
  have hU₀ : ((phiCompactExpHi a:ℚ):ℝ)^16 ≤
      ((expRoundUp ((phiCompactExpHi a)^16) : ℚ):ℝ) := by
    exact_mod_cast hroundU ((phiCompactExpHi a)^16)
  exact ⟨hL₀.trans (hBpow.trans (Real.exp_le_exp.mpr (neg_le_neg hhi))),
    (Real.exp_le_exp.mpr (neg_le_neg hlo)).trans (hApow.trans hU₀)⟩

#print axioms phiCompactExpBox_containsReal

end Nuttall
