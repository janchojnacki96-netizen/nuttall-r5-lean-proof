import W5.ThetaAuditedOriginalFullTail

/-!
# Uniform original theta tail from index four on the second cell

This module reuses the EXISTING universal all-entry n^26 Gaussian
majorant and half-ratio summability. The general audited constant
is extremely loose for n=2 or n=3, but already gives a tiny tail
as soon as n>=4 and x<=177/512.

No new Gaussian ratio estimate, integral, or infinite-series
machinery is introduced. For the whole second cell, and EVERY
one of the 25 genuine theta coefficients, the true infinite
tail after n=3 is smaller than 10^(-12).

The n=2 and n=3 true terms remain separate finite obligations.
-/

namespace W5

/-- On the entire second original audited cell and all smaller
positive x, the reciprocal-square parameter is at least eight. -/
theorem thetaSecondCell_y_ge_eight
    (x : ℝ) (hx : 0 < x) (hxb : x ≤ (177:ℝ)/512) :
    (8:ℝ) ≤ 1/x^2 := by
  have hp : 0 ≤ ((177:ℝ)/512-x)*((177:ℝ)/512+x) :=
    mul_nonneg (by linarith) (by linarith)
  apply (le_div_iff₀ (sq_pos_of_pos hx)).2
  nlinarith [hp]

/-- Finite Mathlib exponential Taylor certificate for the
N=4, y=8 head of the *already proved* general all-entry bound.
A single 100th Taylor term avoids any interval exponential oracle. -/
theorem thetaSecondCell_generalMajorant_head_four_lt_oneE12 :
    ((2*5*4096*30000000000 : ℝ) *
       (4:ℝ)^26 * (8:ℝ)^4) *
       Real.exp (-120) < 1/(10:ℝ)^12 := by
  let M : ℝ := (2*5*4096*30000000000 : ℝ) * (4:ℝ)^26 * (8:ℝ)^4
  have hfinite :
      M*(10:ℝ)^12 <
        (120:ℝ)^100/(Nat.factorial 100 : ℝ) := by
    dsimp [M]
    norm_num
  have hexp :
      (120:ℝ)^100/(Nat.factorial 100 : ℝ) ≤ Real.exp 120 :=
    Real.pow_div_factorial_le_exp 120 (by norm_num) 100
  have hE : 0 < Real.exp 120 := Real.exp_pos 120
  have hden : (0:ℝ) < (10:ℝ)^12 := by positivity
  have hM : M / Real.exp 120 < 1/(10:ℝ)^12 := by
    apply (div_lt_iff₀ hE).mpr
    calc
      M < Real.exp 120/(10:ℝ)^12 :=
        (lt_div_iff₀ hden).mpr (hfinite.trans_le hexp)
      _ = (1/(10:ℝ)^12) * Real.exp 120 := by ring
  simpa only [M, Real.exp_neg, div_eq_mul_inv] using hM

/-- The full n>=4 absolute majorant is tiny at y=8.
All nontrivial series reasoning comes from the old half-ratio lemma. -/
theorem thetaSecondCell_generalMajorant_tsum_four_lt_oneE12 :
    ((5*4096*30000000000 : ℝ) * (8:ℝ)^4) *
      (∑' k : ℕ, thetaMajorantTerm 8 (4+k)) <
        1/(10:ℝ)^12 := by
  have hbound :=
    thetaMajorantTerm_tsum_tail_le_twice_first
      4 (by norm_num) 8 (by norm_num)
  calc
    _ ≤ ((5*4096*30000000000 : ℝ) * (8:ℝ)^4) *
          (2 * thetaMajorantTerm 8 4) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ((2*5*4096*30000000000 : ℝ) *
          (4:ℝ)^26*(8:ℝ)^4) * Real.exp (-120) := by
      norm_num [thetaMajorantTerm]
      ring
    _ < _ := thetaSecondCell_generalMajorant_head_four_lt_oneE12

/-- The *genuine* n>=4 theta coefficient tail is below 10^-12
uniformly for ALL 25 entries on the complete second cell.
No assumptions on individual moment quadrature or 768-bit
matrices: this is inherited from already proved Mathlib Gaussian
majorants and a single finite exact-rational Taylor comparison. -/
theorem thetaSecondCell_allEntriesTail_four_abs_lt_oneE12
    (x : ℝ) (hx : 0 < x)
    (hxb : x ≤ (177:ℝ)/512) (i j : Fin 5) :
    |thetaAuditedTail 4 x i j| < 1/(10:ℝ)^12 := by
  have hx1 : x ≤ 1 := by linarith
  have hy : (8:ℝ) ≤ 1/x^2 :=
    thetaSecondCell_y_ge_eight x hx hxb
  have htail :=
    thetaAuditedTail_abs_le_majorant_tsum
      4 (by norm_num) x hx hx1 (by linarith) i j
  have huniform :=
    thetaMajorantTerm_uniform_tail
      4 (by norm_num) 8 (1/x^2) (by norm_num) hy
  have hscaled :
      (5*4096*30000000000 : ℝ) *
        ((1/x^2)^4 *
          (∑' k : ℕ, thetaMajorantTerm (1/x^2) (4+k))) ≤
      (5*4096*30000000000 : ℝ) *
        ((8:ℝ)^4 *
          (∑' k : ℕ, thetaMajorantTerm 8 (4+k))) :=
    mul_le_mul_of_nonneg_left huniform (by norm_num)
  calc
    |thetaAuditedTail 4 x i j| ≤
        ((5*4096*30000000000 : ℝ)*(1/x^2)^4) *
          (∑' k : ℕ, thetaMajorantTerm (1/x^2) (4+k)) := htail
    _ = (5*4096*30000000000 : ℝ) *
          ((1/x^2)^4 *
            (∑' k : ℕ, thetaMajorantTerm (1/x^2) (4+k))) := by ring
    _ ≤ (5*4096*30000000000 : ℝ) *
          ((8:ℝ)^4 *
            (∑' k : ℕ, thetaMajorantTerm 8 (4+k))) := hscaled
    _ = ((5*4096*30000000000 : ℝ)*(8:ℝ)^4) *
          (∑' k : ℕ, thetaMajorantTerm 8 (4+k)) := by ring
    _ < 1/(10:ℝ)^12 :=
      thetaSecondCell_generalMajorant_tsum_four_lt_oneE12

end W5
