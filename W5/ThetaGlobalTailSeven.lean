import W5.ThetaThirdCellTailFive

/-!
# A universal original theta tail certificate after only SIX indices

For every 0 < x <= 145/256, the preexisting verified monotonicity
lemma gives 3 <= 1/x^2. The CI-green generic fixed-y0 tail theorem
from PR #144 then reduces the TRUE original n>=7 infinite theta
series to ONE head at n=7, y0=3.

That head contains exp(-144) and has an exact Mathlib one-term
factorial certificate (N=144). We can therefore reuse a seven-term
prefix instead of the original 12-term prefix whenever a NEW
rational LDL matrix tolerates an error of 10^-20.

The earlier stronger 10^-35 tail at n>=12 remains necessary
when matching the original tighter 768-bit auditor endpoints.
This module does NOT claim containment in those endpoints.
-/

namespace W5

/-- Uniformly small N=7 y=3 Gaussian head: all arithmetic except
Real.exp is decided exactly by Mathlib's factorial and norm_num. -/
theorem thetaGlobal_tail_seven_head_lt_oneE20 :
    ((2*5*4096*30000000000 : ℝ) *
       (7:ℝ)^26 * (3:ℝ)^4) *
       Real.exp (-144) < 1/(10:ℝ)^20 := by
  let M : ℝ :=
    (2*5*4096*30000000000 : ℝ) * (7:ℝ)^26 * (3:ℝ)^4
  have hfinite :
      M*(10:ℝ)^20 <
        (144:ℝ)^144/(Nat.factorial 144 : ℝ) := by
    dsimp [M]
    norm_num
  have hexp :
      (144:ℝ)^144/(Nat.factorial 144 : ℝ) ≤ Real.exp 144 :=
    Real.pow_div_factorial_le_exp 144 (by norm_num) 144
  have hE : 0 < Real.exp 144 := Real.exp_pos 144
  have hden : (0:ℝ) < (10:ℝ)^20 := by positivity
  have hM : M / Real.exp 144 < 1/(10:ℝ)^20 := by
    apply (div_lt_iff₀ hE).mpr
    calc
      M < Real.exp 144/(10:ℝ)^20 :=
        (lt_div_iff₀ hden).mpr (hfinite.trans_le hexp)
      _ = (1/(10:ℝ)^20) * Real.exp 144 := by ring
  simpa only [M, Real.exp_neg, div_eq_mul_inv] using hM

/-- The existing half-ratio bound controls every n>=7 term. -/
theorem thetaGlobal_tail_seven_tsum_lt_oneE20 :
    ((5*4096*30000000000 : ℝ) * (3:ℝ)^4) *
      (∑' k : ℕ, thetaMajorantTerm 3 (7+k)) <
        1/(10:ℝ)^20 := by
  have hbound :=
    thetaMajorantTerm_tsum_tail_le_twice_first
      7 (by norm_num) 3 (by norm_num)
  calc
    _ ≤ ((5*4096*30000000000 : ℝ) * (3:ℝ)^4) *
          (2 * thetaMajorantTerm 3 7) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ((2*5*4096*30000000000 : ℝ) *
          (7:ℝ)^26*(3:ℝ)^4) * Real.exp (-144) := by
      norm_num [thetaMajorantTerm]
      ring
    _ < _ := thetaGlobal_tail_seven_head_lt_oneE20

/-- Every one of the 25 ORIGINAL theta coefficient series has its
genuine n>=7 tail uniformly bounded by 10^-20 on the COMPLETE
Nuttall R5 compact x-domain. No cell, coefficient, numeric checker
or external interval assumption remains in this theorem. -/
theorem thetaGlobal_allEntriesTail_seven_abs_lt_oneE20
    (x : ℝ) (hx : 0 < x)
    (hxb : x ≤ (145:ℝ)/256) (i j : Fin 5) :
    |thetaAuditedTail 7 x i j| < 1/(10:ℝ)^20 := by
  have hx1 : x ≤ 1 := by linarith
  have hy : (3:ℝ) ≤ 1/x^2 :=
    thetaAuditor_y_ge_three x hx hxb
  exact
    (thetaOriginalTail_abs_le_fixed_reciprocal
      7 (by norm_num) 3 (by norm_num)
      x hx hx1 hy i j).trans_lt
      thetaGlobal_tail_seven_tsum_lt_oneE20

end W5
