import W5.ThetaAuditedOriginalFullTail
import W5.ThetaAuditedMajorantGeometricTail
import W5.ThetaAuditedMajorantUniformParameter

/-!
# Genuine original theta n>=5 tail on the third x-cell

The existing universal Gaussian majorant and the Mathlib-proved
geometric tail work at ANY square-index cutoff N>=2 and for
ANY lower reciprocal-square parameter y0>=3.

Instead of repeating the original analytic/summability proofs,
prove a short generic comparison once. Then specialize to N=5,
y0=6, which covers the original third audited x-cell
[177/512,821/2048] and yields a strict 10^(-12) real-series tail.

The low indices n=2,3,4 must still be controlled individually
before this proves a complete third-cell original theta sign result.
-/

namespace W5

/-- A generic uniform bound on the ACTUAL infinite theta tail.
The numerical right side depends only on N and a lower bound y0
for 1/x², not on the individual matrix coefficient or on x. -/
theorem thetaOriginalTail_abs_le_fixed_reciprocal
    (N : ℕ) (hN : 2 ≤ N)
    (y0 : ℝ) (hy0 : 3 ≤ y0)
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : y0 ≤ 1/x^2) (i j : Fin 5) :
    |thetaAuditedTail N x i j| ≤
      ((5*4096*30000000000 : ℝ)*y0^4) *
        (∑' k : ℕ, thetaMajorantTerm y0 (N+k)) := by
  have hy3 : (3:ℝ) ≤ 1/x^2 := hy0.trans hy
  have htail :=
    thetaAuditedTail_abs_le_majorant_tsum N hN
      x hx hx1 hy3 i j
  have hparameter :=
    thetaMajorantTerm_uniform_tail N hN y0 (1/x^2) hy0 hy
  calc
    |thetaAuditedTail N x i j| ≤
        ((5*4096*30000000000 : ℝ)*(1/x^2)^4) *
          (∑' k : ℕ, thetaMajorantTerm (1/x^2) (N+k)) :=
      htail
    _ = (5*4096*30000000000 : ℝ) *
          ((1/x^2)^4 *
            (∑' k : ℕ, thetaMajorantTerm (1/x^2) (N+k))) := by ring
    _ ≤ (5*4096*30000000000 : ℝ) *
          (y0^4 * (∑' k : ℕ, thetaMajorantTerm y0 (N+k))) :=
      mul_le_mul_of_nonneg_left hparameter (by norm_num)
    _ = ((5*4096*30000000000 : ℝ)*y0^4) *
          (∑' k : ℕ, thetaMajorantTerm y0 (N+k)) := by ring

/-- The third audited endpoint lies strictly below 1/sqrt(6).
This is a purely rational inequality, independent of theta. -/
theorem thetaThirdCell_y_ge_six
    (x : ℝ) (hx : 0 < x) (hxb : x ≤ (821:ℝ)/2048) :
    (6:ℝ) ≤ 1/x^2 := by
  have hx2 : 0 < x^2 := sq_pos_of_pos hx
  have hsq : x^2 ≤ ((821:ℝ)/2048)^2 :=
    pow_le_pow_left₀ hx.le hxb 2
  apply (le_div_iff₀ hx2).mpr
  nlinarith [hsq]

/-- An exact Mathlib exponential/Taylor comparison, with ample slack.
The N=5, y0=6 Gaussian head is smaller than 10^-12 even after
the preexisting universal n^26 factor and the factor-of-two tail. -/
theorem thetaThirdCell_majorant_head_five_lt_oneE12 :
    ((2*5*4096*30000000000 : ℝ) *
       (5:ℝ)^26 * (6:ℝ)^4) *
       Real.exp (-144) < 1/(10:ℝ)^12 := by
  let M : ℝ :=
    (2*5*4096*30000000000 : ℝ) * (5:ℝ)^26 * (6:ℝ)^4
  have hfinite :
      M*(10:ℝ)^12 <
        (144:ℝ)^80/(Nat.factorial 80 : ℝ) := by
    dsimp [M]
    norm_num
  have hexp :
      (144:ℝ)^80/(Nat.factorial 80 : ℝ) ≤ Real.exp 144 :=
    Real.pow_div_factorial_le_exp 144 (by norm_num) 80
  have hE : 0 < Real.exp 144 := Real.exp_pos 144
  have hden : (0:ℝ) < (10:ℝ)^12 := by positivity
  have hM : M / Real.exp 144 < 1/(10:ℝ)^12 := by
    apply (div_lt_iff₀ hE).mpr
    calc
      M < Real.exp 144/(10:ℝ)^12 :=
        (lt_div_iff₀ hden).mpr (hfinite.trans_le hexp)
      _ = (1/(10:ℝ)^12) * Real.exp 144 := by ring
  simpa only [M, Real.exp_neg, div_eq_mul_inv] using hM

/-- The exact geometric half-ratio bound from Mathlib gives a
small numerical majorant for all infinitely many n>=5 terms. -/
theorem thetaThirdCell_majorant_tsum_five_lt_oneE12 :
    ((5*4096*30000000000 : ℝ) * (6:ℝ)^4) *
      (∑' k : ℕ, thetaMajorantTerm 6 (5+k)) <
        1/(10:ℝ)^12 := by
  have hbound :=
    thetaMajorantTerm_tsum_tail_le_twice_first
      5 (by norm_num) 6 (by norm_num)
  calc
    _ ≤ ((5*4096*30000000000 : ℝ) * (6:ℝ)^4) *
          (2 * thetaMajorantTerm 6 5) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ((2*5*4096*30000000000 : ℝ) *
          (5:ℝ)^26*(6:ℝ)^4) * Real.exp (-144) := by
      norm_num [thetaMajorantTerm]
      ring
    _ < _ := thetaThirdCell_majorant_head_five_lt_oneE12

/-- A TRUE analytic bound for the original infinite series tail n>=5,
simultaneously for every one of the 25 Nuttall theta coefficients.
There are no finite-term or numerical oracle hypotheses. -/
theorem thetaThirdCell_allEntriesTail_five_abs_lt_oneE12
    (x : ℝ) (hx : 0 < x)
    (hxb : x ≤ (821:ℝ)/2048) (i j : Fin 5) :
    |thetaAuditedTail 5 x i j| < 1/(10:ℝ)^12 := by
  have hx1 : x ≤ 1 := by linarith
  have hy : (6:ℝ) ≤ 1/x^2 :=
    thetaThirdCell_y_ge_six x hx hxb
  exact
    (thetaOriginalTail_abs_le_fixed_reciprocal
      5 (by norm_num) 6 (by norm_num)
      x hx hx1 hy i j).trans_lt
      thetaThirdCell_majorant_tsum_five_lt_oneE12

end W5
