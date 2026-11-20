import W5.ThetaTermwiseCellRealCertificates
import Mathlib.Analysis.Complex.Exponential

/-!
# Exact 65-term Taylor enclosure for exp on the auditor's reduced domain

The original independent 768-bit certificate uses a 65-term partial
sum S_64(z) = Σ_{k=0}^{64} z^k/k! after power-of-two range reduction,
and adds an outward remainder no larger than 2/(3^65 · 65!).

We do not reprove convergence or Taylor's theorem for exp. Mathlib
already proves `Real.sum_le_exp_of_nonneg` and `Real.exp_bound'`.
We specialize those to 0 ≤ z ≤ 1/3 and N = 65, and check the small
rational factor 66/65 ≤ 2.

This is an actual analytic bound for REAL exp, not an assumption.
The separate task of implementing its 768-bit integer interval
evaluation and showing that the auditor's rounded partial sum contains
this mathematical Taylor polynomial remains open.
-/

namespace W5

/-- Exactly the 65 terms used by the 768-bit integer auditor. -/
noncomputable def thetaExpTaylor65 (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 65, z^k / (Nat.factorial k : ℝ)

/-- A nonnegative exponential argument in the auditor's reduced
range has a mathematically rigorous 65-term Taylor enclosure,
with EXACTLY the fixed remainder bound used by the integer code. -/
theorem thetaExpTaylor65_bounds
    (z : ℝ) (hz : 0 ≤ z) (hthird : z ≤ (1:ℝ)/3) :
    thetaExpTaylor65 z ≤ Real.exp z ∧
      Real.exp z ≤
        thetaExpTaylor65 z +
          2 / ((3:ℝ)^65 * (Nat.factorial 65 : ℝ)) := by
  have hz1 : z ≤ 1 := by linarith
  have hfactorial : (0 : ℝ) < (Nat.factorial 65 : ℝ) := by
    positivity
  have hpartial :
      thetaExpTaylor65 z ≤ Real.exp z := by
    simpa only [thetaExpTaylor65] using
      (Real.sum_le_exp_of_nonneg hz 65)
  have hbound :
      Real.exp z ≤ thetaExpTaylor65 z +
        z^65 * ((66:ℝ) /
          ((Nat.factorial 65 : ℝ) * 65)) := by
    have hraw := Real.exp_bound' hz hz1 (n := 65) (by norm_num)
    change Real.exp z ≤
      (∑ m ∈ Finset.range 65, z^m / (Nat.factorial m : ℝ)) +
        z^65 * ((66:ℝ) / ((Nat.factorial 65 : ℝ) * 65))
    convert hraw using 1 <;> ring
  have hpower : z^65 ≤ ((1:ℝ)/3)^65 :=
    pow_le_pow_left₀ hz hthird 65
  have hcoef :
      (66:ℝ) / ((Nat.factorial 65 : ℝ) * 65) ≤
      2 / (Nat.factorial 65 : ℝ) := by
    have hnum : (66:ℝ) / 65 ≤ 2 := by norm_num
    calc
      (66:ℝ) / ((Nat.factorial 65 : ℝ) * 65) =
          ((66:ℝ) / 65) / (Nat.factorial 65 : ℝ) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ 2 / (Nat.factorial 65 : ℝ) :=
        div_le_div_of_nonneg_right hnum hfactorial.le
  have hnonnegcoef :
      (0:ℝ) ≤ (66:ℝ) / ((Nat.factorial 65 : ℝ) * 65) := by
    positivity
  have herror :
      z^65 * ((66:ℝ) / ((Nat.factorial 65 : ℝ) * 65)) ≤
        2 / ((3:ℝ)^65 * (Nat.factorial 65 : ℝ)) := by
    calc
      z^65 * ((66:ℝ) / ((Nat.factorial 65 : ℝ) * 65)) ≤
          ((1:ℝ)/3)^65 *
            ((66:ℝ) / ((Nat.factorial 65 : ℝ) * 65)) :=
        mul_le_mul_of_nonneg_right hpower hnonnegcoef
      _ ≤ ((1:ℝ)/3)^65 * (2 / (Nat.factorial 65 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = 2 / ((3:ℝ)^65 * (Nat.factorial 65 : ℝ)) := by
        simp only [one_div, div_eq_mul_inv, inv_pow, mul_inv_rev]
        ring
  exact ⟨hpartial, hbound.trans (add_le_add_right herror _)⟩

/-- Direct soundness of a real interval enclosing the exact
65-term partial sum, with the already Mathlib-certified remainder
added. This gives a reusable link between rounded partial sums
and the TRUE exponential, but does not fabricate any rounded data. -/
theorem thetaExpTaylor65_interval_contains_real_exp
    (z : ℝ) (hz : 0 ≤ z) (hthird : z ≤ (1:ℝ)/3)
    (P : QInterval)
    (hP : QInterval.ContainsReal P (thetaExpTaylor65 z)) :
    ((P.lo : ℝ) ≤ Real.exp z) ∧
      (Real.exp z ≤ (P.hi : ℝ) +
        2 / ((3:ℝ)^65 * (Nat.factorial 65 : ℝ))) := by
  obtain ⟨hlo, hhi⟩ := thetaExpTaylor65_bounds z hz hthird
  exact ⟨hP.1.trans hlo, hhi.trans (add_le_add_left hP.2 _)⟩

end W5
