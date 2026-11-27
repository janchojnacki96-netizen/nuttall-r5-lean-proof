import Nuttall.ShiftedThetaAlgebra
import Nuttall.TailMoments

namespace Nuttall

open Set
open scoped BigOperators

/-- The contribution of one index to the shifted weight. The zero index
drops out, and the strict cutoff agrees with the text of Section 4.1. -/
noncomputable def shiftedMomentTerm (j n : ℕ) (u : ℝ) : ℝ :=
  if 0 < n ∧ thetaKnot n < u then
    tailMomentWeight j (u-thetaKnot n) / Real.sqrt (n : ℝ)
  else 0

private theorem shiftedMomentTerm_hasSum (j : ℕ) (u : ℝ) :
    HasSum (fun n => shiftedMomentTerm j n u)
      (∑ n ∈ Finset.range ⌈Real.exp (2*u)⌉₊, shiftedMomentTerm j n u) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  unfold shiftedMomentTerm
  apply if_neg
  rintro ⟨hn0, hk⟩
  exact hn (Finset.mem_range.mpr (Nat.lt_ceil.2 ((thetaKnot_lt_iff n hn0 u).1 hk)))

/-- The shifted sum can be truncated exactly at the ceiling of `exp (2*u)`. -/
theorem shiftedMomentTerm_tsum_eq_sum (j : ℕ) (u : ℝ) :
    (∑' n, shiftedMomentTerm j n u) =
      ∑ n ∈ Finset.range ⌈Real.exp (2*u)⌉₊, shiftedMomentTerm j n u :=
  (shiftedMomentTerm_hasSum j u).tsum_eq

theorem shiftedMomentTerm_summable (j : ℕ) (u : ℝ) :
    Summable (fun n => shiftedMomentTerm j n u) :=
  (shiftedMomentTerm_hasSum j u).summable

/-- Cutoffs can be placed inside the columns of the determinant. -/
theorem det_shiftedMomentTerm_eq_indicator {p : ℕ} (k n : Fin p → ℕ)
    (hn : ∀ i, 0 < n i) (u : Fin p → ℝ) :
    (Matrix.of (fun (i j : Fin p) => shiftedMomentTerm (k i) (n j) (u j))).det =
      (univ.pi (fun j => Ioi (thetaKnot (n j)))).indicator
        (fun x => (Matrix.of (fun (i j : Fin p) =>
          tailMomentWeight (k i) (x j-thetaKnot (n j)) / Real.sqrt (n j : ℝ))).det) u := by
  by_cases h : ∀ j, thetaKnot (n j) < u j
  · have hm : u ∈ univ.pi (fun j => Ioi (thetaKnot (n j))) := by
      simpa only [mem_univ_pi, mem_Ioi] using h
    rw [indicator_of_mem hm]
    congr 1
    ext i j
    simp [shiftedMomentTerm, hn j, h j]
  · have hm : u ∉ univ.pi (fun j => Ioi (thetaKnot (n j))) := by
      simpa only [mem_univ_pi, mem_Ioi] using h
    rw [indicator_of_notMem hm]
    push Not at h
    obtain ⟨j, hj⟩ := h
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    simp [shiftedMomentTerm, not_lt_of_ge hj]

#print axioms shiftedMomentTerm_tsum_eq_sum
#print axioms det_shiftedMomentTerm_eq_indicator

end Nuttall
