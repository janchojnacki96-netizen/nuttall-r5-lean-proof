import W5.ThetaAuditedMajorantGeometricTail
import Mathlib.Analysis.Complex.Exponential

/-!
# Fully analytic 1e-35 NUMERICAL bounds for BOTH audited majorant tails

The standalone Python audit checks the constant
  2 * 5 * 4096 * 30000000000 * N^26 * y^4
    * exp (-((N^2 - 1)*y)) < 1e-35
for (N,y)=(12,3) and (2,64).

We prove these inequalities in Lean using just the existing
Mathlib lower bound `Real.pow_div_factorial_le_exp` with the
SINGLE 100th Taylor term of exp(E), rather than auditing a new
transcendental interval implementation.

Together with the earlier CI-verified half-ratio inequality,
this certifies the entire REAL infinite tail of the EXPLICIT
polynomial-Gaussian majorant, including its exact prefactor.

Still missing: a real theorem bounding each genuine original
thetaCoefficient omitted summand by this majorant. This module
does not assert the real 51x15 analytic entry enclosures.
-/

namespace W5

/-- Using one nonnegative Taylor coefficient of exp(E) is enough to
bound exp(-E) from above whenever a finite exact-rational inequality
is verified. Mathlib supplies the exponential bound. -/
private theorem numeric_exp_decay_from_one_factorial
    (E M : ℝ) (hE : 0 ≤ E)
    (hfinite : M * (10 : ℝ)^35 <
      E^100 / (Nat.factorial 100 : ℝ)) :
    M * Real.exp (-E) < 1 / (10 : ℝ)^35 := by
  have hlower : E^100 / (Nat.factorial 100 : ℝ) ≤ Real.exp E :=
    Real.pow_div_factorial_le_exp hE 100
  have hpos : 0 < Real.exp E := Real.exp_pos E
  have hden : 0 < (10 : ℝ)^35 := by positivity
  have hprod : M * (10 : ℝ)^35 < Real.exp E :=
    hfinite.trans_le hlower
  have hbound : M < Real.exp E / (10 : ℝ)^35 :=
    (lt_div_iff₀ hden).mpr hprod
  have hquot : M / Real.exp E < 1 / (10 : ℝ)^35 := by
    apply (div_lt_iff₀ hpos).mpr
    calc
      M < Real.exp E / (10 : ℝ)^35 := hbound
      _ = (1 / (10 : ℝ)^35) * Real.exp E := by ring
  simpa only [Real.exp_neg, div_eq_mul_inv] using hquot

/-- Finite rational calculation for near cells:
the n=12 head majorant, including the auditor's factor of two,
is strictly smaller than 10^-35, independently of any floating
point arithmetic. The 100th Taylor term of exp 429 suffices. -/
theorem thetaAuditorNearTailFirst_lt_oneE35 :
    ((2*5*4096*30000000000 : ℝ) * (12 : ℝ)^26 * (3 : ℝ)^4) *
      Real.exp (-429) < 1 / (10 : ℝ)^35 := by
  exact numeric_exp_decay_from_one_factorial 429
    ((2*5*4096*30000000000 : ℝ) * (12 : ℝ)^26 * (3 : ℝ)^4)
    (by norm_num) (by norm_num)

/-- Finite rational calculation for far cells:
the n=2 head majorant with y=64 is likewise < 10^-35.
The same one-term Mathlib bound for exp 192 suffices. -/
theorem thetaAuditorFarTailFirst_lt_oneE35 :
    ((2*5*4096*30000000000 : ℝ) * (2 : ℝ)^26 * (64 : ℝ)^4) *
      Real.exp (-192) < 1 / (10 : ℝ)^35 := by
  exact numeric_exp_decay_from_one_factorial 192
    ((2*5*4096*30000000000 : ℝ) * (2 : ℝ)^26 * (64 : ℝ)^4)
    (by norm_num) (by norm_num)

/-- One complete infinite series numerical inequality for the near
regime. The summability and geometric bound were already proved by
reusing the earlier half-ratio and Mathlib's geometric series. -/
theorem thetaAuditorNearMajorantTsum_lt_oneE35 :
    ((5*4096*30000000000 : ℝ) * (3 : ℝ)^4) *
      (∑' k : ℕ, thetaMajorantTerm 3 (12+k)) <
        1 / (10 : ℝ)^35 := by
  have hC : 0 ≤ (5*4096*30000000000 : ℝ) * (3 : ℝ)^4 := by
    positivity
  calc
    ((5*4096*30000000000 : ℝ) * (3 : ℝ)^4) *
        (∑' k : ℕ, thetaMajorantTerm 3 (12+k)) ≤
      ((5*4096*30000000000 : ℝ) * (3 : ℝ)^4) *
        (2 * thetaMajorantTerm 3 12) :=
      mul_le_mul_of_nonneg_left thetaMajorantTerm_near_tail_bound hC
    _ = ((2*5*4096*30000000000 : ℝ) *
        (12 : ℝ)^26 * (3 : ℝ)^4) * Real.exp (-429) := by
      norm_num [thetaMajorantTerm]
      ring
    _ < 1 / (10 : ℝ)^35 := thetaAuditorNearTailFirst_lt_oneE35

/-- Analogous full infinite majorant bound for far cells. -/
theorem thetaAuditorFarMajorantTsum_lt_oneE35 :
    ((5*4096*30000000000 : ℝ) * (64 : ℝ)^4) *
      (∑' k : ℕ, thetaMajorantTerm 64 (2+k)) <
        1 / (10 : ℝ)^35 := by
  have hC : 0 ≤ (5*4096*30000000000 : ℝ) * (64 : ℝ)^4 := by
    positivity
  calc
    ((5*4096*30000000000 : ℝ) * (64 : ℝ)^4) *
        (∑' k : ℕ, thetaMajorantTerm 64 (2+k)) ≤
      ((5*4096*30000000000 : ℝ) * (64 : ℝ)^4) *
        (2 * thetaMajorantTerm 64 2) :=
      mul_le_mul_of_nonneg_left thetaMajorantTerm_far_tail_bound hC
    _ = ((2*5*4096*30000000000 : ℝ) *
        (2 : ℝ)^26 * (64 : ℝ)^4) * Real.exp (-192) := by
      norm_num [thetaMajorantTerm]
      ring
    _ < 1 / (10 : ℝ)^35 := thetaAuditorFarTailFirst_lt_oneE35

end W5
