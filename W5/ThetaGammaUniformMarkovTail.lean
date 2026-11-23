import W5.ThetaMomentFourthRootChordTangent
import W5.ThetaAuditedCorrectionMoment

/-!
# Uniform polynomial Markov domination for the Gamma integration tail

The new high-precision weighted Γ quadrature integrates w∈[0,H]
using arbitrarily many short bins. The remaining w>H half-line
should have ONE rigorous common bound, independent of the 48 theta
x-cells and all nine weighted Γ moment indices.

For every H>0, w≥H, q≥0, k,m∈ℕ prove POINTWISE:

 e^(-w) w^k (1+qw)^(1/4)
    ≤ e^(-w) w^(k+m) (1+qw/4) / H^m.

This follows from Mathlib's already-verified fourth-root tangent
and monotonicity H^m≤w^m. Integration then reduces to the existing
Mathlib-backed factorial Gamma moments of degrees k+m and k+m+1.

In particular H=128 and m=120 produce a provably tiny uniform
rational *candidate budget* for k=0,...,8. This module deliberately
does NOT confuse a pointwise domination with the later, still-needed
integral-mono proof for the actual infinite tail.
-/

namespace W5

/-- One analytic inequality for all weighted Gamma tail indices.
No external numeric approximation, x-cell split or special k-case. -/
theorem thetaGammaTailMarkov_pointwise
    (q H w : ℝ) (k m : ℕ)
    (hq : 0 ≤ q) (hH : 0 < H) (hHw : H ≤ w) :
    (Real.exp (-w) * w^k) * (1+q*w)^((1:ℝ)/4) ≤
      (Real.exp (-w) * w^(k+m) * (1+q*w/4)) / H^m := by
  have hw : 0 ≤ w := hH.le.trans hHw
  have hroot :
      (1+q*w)^((1:ℝ)/4) ≤ 1+q*w/4 := by
    simpa only [mul_zero, add_zero, Real.one_rpow,
      sub_zero, one_pow, mul_one] using
      (thetaQuarterRoot_tangent_on_bin q 0 w hq
        (by norm_num) hw)
  have hpow : H^m ≤ w^m :=
    pow_le_pow_left₀ hH.le hHw m
  have hden : 0 < H^m := pow_pos hH m
  have hmass : 0 ≤ Real.exp (-w) * w^k :=
    mul_nonneg (Real.exp_nonneg _) (pow_nonneg hw k)
  have hupper : 0 ≤ 1+q*w/4 := by positivity
  have hpositive :
      0 ≤ (Real.exp (-w) * w^k) * (1+q*w/4) :=
    mul_nonneg hmass hupper
  calc
    (Real.exp (-w) * w^k) * (1+q*w)^((1:ℝ)/4) ≤
        (Real.exp (-w) * w^k) * (1+q*w/4) :=
      mul_le_mul_of_nonneg_left hroot hmass
    _ ≤ (Real.exp (-w) * w^(k+m) * (1+q*w/4)) / H^m := by
      apply (le_div_iff₀ hden).2
      calc
        ((Real.exp (-w) * w^k) * (1+q*w/4)) * H^m =
            H^m * ((Real.exp (-w) * w^k) * (1+q*w/4)) := by ring
        _ ≤ w^m * ((Real.exp (-w) * w^k) * (1+q*w/4)) :=
          mul_le_mul_of_nonneg_right hpow hpositive
        _ = Real.exp (-w) * w^(k+m) * (1+q*w/4) := by
          rw [pow_add]
          ring

/-- Exact rational factorial/Markov budget for q≤1 at cutoff
H=128, auxiliary exponent m=120. Once integrated using the
existing Gamma factorial identity, this bounds the real w-tail. -/
def thetaGammaMarkovTailBudget (k : ℕ) : ℚ :=
  ((Nat.factorial (k+120) : ℚ) +
      (Nat.factorial (k+121) : ℚ)/4) / (128:ℚ)^120

/-- ONE exact rational computation handles ALL nine moments.
The mathematical implication from the real tail integral to
this budget is still separate; this checks the NUMERIC budget. -/
theorem thetaGammaMarkovTailBudget_allNine_lt_oneE30 :
    ∀ k : Fin 9,
      thetaGammaMarkovTailBudget k.val < (1:ℚ)/(10:ℚ)^30 := by
  native_decide

end W5
