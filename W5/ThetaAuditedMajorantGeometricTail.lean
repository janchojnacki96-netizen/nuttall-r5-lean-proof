import W5.TailRatioGeneral
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A quantitative REAL infinite-tail bound from the EXISTING half-ratio

The certificate's integer audit uses polynomial/exponential
majorants of the form

  a(n,y) = n^26 * exp(-((n^2-1)*y)),  n>=2, y>=3.

Earlier project lemmas `theta_majorant_half_ratio` and
`theta_tail_ratio_numerical` already proved
a(n+1,y) < (1/2)*a(n,y) uniformly. Rather than repeat any
of that analysis, we compose it with Mathlib's proved
`hasSum_geometric_two` and summable comparison theorem.

Result:
  sum_{k>=0} a(N+k,y) <= 2*a(N,y)

for every integer N>=2 and real y>=3, including BOTH exact
auditor tail regimes (N,y)=(12,3) and (2,64).

This closes the geometric-series part of the auditor's real
tail majorant. Still open: the original theta coefficient
tail's explicit domination by the majorant and the 1e-35
end-point numerical inequalities. No new postulates.
-/

namespace W5

/-- The already-studied polynomial-Gaussian tail majorant. -/
noncomputable def thetaMajorantTerm (y : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)^26 * Real.exp (-(((n : ℝ)^2 - 1)*y))

private theorem thetaMajorantTerm_nonneg (y : ℝ) (n : ℕ) :
    0 ≤ thetaMajorantTerm y n := by
  unfold thetaMajorantTerm
  positivity

/-- Reuse the precise, already proved real half-ratio theorem,
without any further numerical exponential argument. -/
theorem thetaMajorantTerm_succ_le_half
    (n : ℕ) (hn : 2 ≤ n) (y : ℝ) (hy : 3 ≤ y) :
    thetaMajorantTerm y (n+1) ≤
      (1/2 : ℝ) * thetaMajorantTerm y n := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simpa only [thetaMajorantTerm, Nat.cast_succ] using
    (theta_majorant_half_ratio (n : ℝ) y hnr hy).le

/-- The k-th omitted square-index term decreases at least
geometrically from the FIRST omitted term. -/
theorem thetaMajorantTerm_geometric_bound
    (N : ℕ) (hN : 2 ≤ N) (y : ℝ) (hy : 3 ≤ y) :
    ∀ k : ℕ,
      thetaMajorantTerm y (N+k) ≤
        ((1/2 : ℝ)^k) * thetaMajorantTerm y N := by
  intro k
  induction k with
  | zero =>
      simp only [Nat.add_zero, pow_zero, one_mul]
  | succ k ih =>
      have hNk : 2 ≤ N+k := by omega
      have hstep := thetaMajorantTerm_succ_le_half (N+k) hNk y hy
      calc
        thetaMajorantTerm y (N+(k+1)) =
            thetaMajorantTerm y ((N+k)+1) := by
              rw [Nat.add_succ]
        _ ≤ (1/2 : ℝ) * thetaMajorantTerm y (N+k) := hstep
        _ ≤ (1/2 : ℝ) *
            (((1/2 : ℝ)^k) * thetaMajorantTerm y N) :=
              mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = ((1/2 : ℝ)^(k+1)) * thetaMajorantTerm y N := by
              rw [pow_succ]
              ring

/-- Quantitative bound for the ENTIRE REAL infinite majorant tail.
The exact Mathlib geometric series has sum 2. This is not
a bound on the original theta integral yet: that domination
requires a separate analytic theorem. -/
theorem thetaMajorantTerm_tsum_tail_le_twice_first
    (N : ℕ) (hN : 2 ≤ N) (y : ℝ) (hy : 3 ≤ y) :
    (∑' k : ℕ, thetaMajorantTerm y (N+k)) ≤
      2 * thetaMajorantTerm y N := by
  let f : ℕ → ℝ := fun k => thetaMajorantTerm y (N+k)
  let g : ℕ → ℝ := fun k =>
    ((1/2 : ℝ)^k) * thetaMajorantTerm y N
  have hg : HasSum g (2 * thetaMajorantTerm y N) := by
    exact hasSum_geometric_two.mul_right _
  have hfg : ∀ k, f k ≤ g k := by
    intro k
    exact thetaMajorantTerm_geometric_bound N hN y hy k
  have hfnonneg : ∀ k, 0 ≤ f k := by
    intro k
    exact thetaMajorantTerm_nonneg y (N+k)
  have hf : Summable f :=
    Summable.of_nonneg_of_le hfnonneg hfg hg.summable
  exact (hf.tsum_le_tsum hfg hg.summable).trans_eq hg.tsum_eq

/-- Exactly the near-regime first omitted square index 12,
using only the preceding generic theorem. -/
theorem thetaMajorantTerm_near_tail_bound :
    (∑' k : ℕ, thetaMajorantTerm 3 (12+k)) ≤
      2 * thetaMajorantTerm 3 12 :=
  thetaMajorantTerm_tsum_tail_le_twice_first 12
    (by norm_num) 3 (by norm_num)

/-- Exactly the far-regime first omitted square index 2
and the auditor's parameter lower bound y=64. -/
theorem thetaMajorantTerm_far_tail_bound :
    (∑' k : ℕ, thetaMajorantTerm 64 (2+k)) ≤
      2 * thetaMajorantTerm 64 2 :=
  thetaMajorantTerm_tsum_tail_le_twice_first 2
    (by norm_num) 64 (by norm_num)

end W5
