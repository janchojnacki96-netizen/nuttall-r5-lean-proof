import Nuttall.ShiftedMomentCutoff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Nuttall

open MeasureTheory Set
open scoped BigOperators

/-- The shifted sum with a common finite cutoff on the theta indices. -/
noncomputable def shiftedMomentTruncated (j N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, shiftedMomentTerm j n u

/-- The full shifted moment. At each node only finitely many terms contribute. -/
noncomputable def shiftedMoment (j : ℕ) (u : ℝ) : ℝ :=
  ∑' n, shiftedMomentTerm j n u

theorem shiftedMomentTerm_eq_zero_of_ge_ceil (j n : ℕ) (u : ℝ)
    (hn : ⌈Real.exp (2*u)⌉₊ ≤ n) : shiftedMomentTerm j n u = 0 := by
  unfold shiftedMomentTerm
  apply ite_eq_right
  rintro ⟨hn0, hk⟩
  exact (not_lt_of_ge hn) (Nat.lt_ceil.2 ((thetaKnot_lt_iff n hn0 u).1 hk))

theorem shiftedMomentTruncated_eq_of_ge_ceil (j N : ℕ) (u : ℝ)
    (hN : ⌈Real.exp (2*u)⌉₊ ≤ N) :
    shiftedMomentTruncated j N u = shiftedMoment j u := by
  rw [shiftedMomentTruncated, shiftedMoment, shiftedMomentTerm_tsum_eq_sum]
  symm
  exact Finset.sum_subset (Finset.range_mono hN) (fun n _ hn =>
    shiftedMomentTerm_eq_zero_of_ge_ceil j n u
      (Nat.le_of_not_lt (fun h => hn (Finset.mem_range.mpr h))))

theorem abs_shiftedMomentTerm_le (j n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |shiftedMomentTerm j n u| ≤ 2 * Real.exp u := by
  unfold shiftedMomentTerm
  split
  next h =>
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.1
    have ha : 0 ≤ thetaKnot n := div_nonneg (Real.log_nonneg hn) (by norm_num)
    have hw : 0 ≤ u-thetaKnot n := sub_nonneg.mpr h.2.le
    have hdiv : 1 ≤ Real.sqrt (n : ℝ) := by
      simpa using Real.sqrt_le_sqrt hn
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_self (abs_nonneg _) hdiv).trans
    unfold tailMomentWeight
    have h₁ := Real.pow_div_factorial_le_exp _ hw j
    have h₂ := Real.pow_div_factorial_le_exp _ hw (j+1)
    have hex : Real.exp (u-thetaKnot n) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    exact (abs_sub_le _ _).trans (by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      linarith)
  next _ => simpa using (show 0 ≤ 2 * Real.exp u by positivity)

theorem abs_shiftedMomentTruncated_le (j N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |shiftedMomentTruncated j N u| ≤ 4 * Real.exp (3*u) := by
  let M := min N ⌈Real.exp (2*u)⌉₊
  have hMN : M ≤ N := min_le_left _ _
  have hMc : M ≤ ⌈Real.exp (2*u)⌉₊ := min_le_right _ _
  have heq : shiftedMomentTruncated j M u = shiftedMomentTruncated j N u := by
    unfold shiftedMomentTruncated
    apply Finset.sum_subset (Finset.range_mono hMN)
    intro n hn hnm
    apply shiftedMomentTerm_eq_zero_of_ge_ceil
    have h := Finset.mem_range.mp hn
    have h' : M ≤ n := Nat.le_of_not_lt (fun h => hnm (Finset.mem_range.mpr h))
    dsimp [M] at h'
    omega
  rw [← heq, shiftedMomentTruncated]
  have hceil : (M : ℝ) ≤ 2 * Real.exp (2*u) := by
    have h₁ : (M : ℝ) ≤ (⌈Real.exp (2*u)⌉₊ : ℝ) := by exact_mod_cast hMc
    have h₂ := Nat.ceil_lt_add_one (Real.exp_nonneg (2*u))
    have h₃ : 1 ≤ Real.exp (2*u) := Real.one_le_exp (by positivity)
    linarith
  calc
    |∑ n ∈ Finset.range M, shiftedMomentTerm j n u| ≤
        ∑ n ∈ Finset.range M, |shiftedMomentTerm j n u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range M, 2 * Real.exp u :=
      Finset.sum_le_sum (fun n _ => abs_shiftedMomentTerm_le j n hu)
    _ ≤ 4 * Real.exp (3*u) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [show 3*u = 2*u+u by ring, Real.exp_add]
      calc
        (M : ℝ) * (2 * Real.exp u) ≤ (2 * Real.exp (2*u)) * (2 * Real.exp u) :=
          mul_le_mul_of_nonneg_right hceil (by positivity)
        _ = _ := by ring

theorem abs_shiftedMoment_le (j : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |shiftedMoment j u| ≤ 4 * Real.exp (3*u) := by
  rw [← shiftedMomentTruncated_eq_of_ge_ceil j _ u le_rfl]
  exact abs_shiftedMomentTruncated_le j _ hu

/-- A single integrable exponential majorizes any fixed exponential tilt
of the orthant weight. -/
theorem tilted_thetaOrthantWeight_le {X : ℝ} (hX : 0 < X) (A : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (A*u) * thetaOrthantWeight X u ≤
      Real.exp ((A+6)^2/(32*X)) * Real.exp (-u) := by
  rw [thetaOrthantWeight, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hquad : 8*u^2 ≤ Real.exp (4*u) := by
    have h := Real.pow_div_factorial_le_exp _ (show 0 ≤ 4*u by positivity) 2
    norm_num [Nat.factorial] at h
    nlinarith only [h]
  have hmul := mul_le_mul_of_nonneg_left hquad hX.le
  have hs : (A+6)*u - 8*X*u^2 ≤ (A+6)^2/(32*X) := by
    apply (le_div_iff₀ (show 0 < 32*X by positivity)).mpr
    nlinarith only [sq_nonneg (16*X*u-(A+6))]
  linarith only [hs, hmul]

#print axioms abs_shiftedMomentTruncated_le
#print axioms tilted_thetaOrthantWeight_le

end Nuttall
