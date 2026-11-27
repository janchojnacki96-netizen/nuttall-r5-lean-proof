import Nuttall.ShiftTriangularDecay
import Nuttall.MatrixSchurBound
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Nuttall

open MeasureTheory Set intervalIntegral
open scoped BigOperators Matrix.Norms.L2Operator

/-- A positive-distance discrete Gaussian is bounded by the corresponding
Gaussian integral on the positive half-line. -/
theorem sum_shift_gaussian_le (k : ℕ) {N : ℝ} (hN : 0 < N) :
    (∑ m ∈ Finset.range k, Real.exp (-((m:ℝ)+1)^2/N)) ≤
      Real.sqrt (Real.pi*N)/2 := by
  let f (x : ℝ) := Real.exp (-x^2/N)
  have hf : Continuous f := by unfold f; fun_prop
  have hm (m : ℕ) : f ((m:ℝ)+1) ≤ ∫ t in (m:ℝ)..(m:ℝ)+1, f t := by
    have hle : (m:ℝ) ≤ (m:ℝ)+1 := by linarith
    calc
      _ = ∫ _t in (m:ℝ)..(m:ℝ)+1, f ((m:ℝ)+1) := by
        simp [intervalIntegral.integral_const]
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hle (continuous_const.intervalIntegrable _ _)
          (hf.intervalIntegrable _ _)
        intro t ht
        unfold f
        apply Real.exp_le_exp.2
        apply div_le_div_of_nonneg_right _ hN.le
        have ht₀ : 0 ≤ t := (Nat.cast_nonneg _).trans ht.1
        have h := pow_le_pow_left₀ ht₀ ht.2 2
        linarith
  have hs : (∑ m ∈ Finset.range k, f ((m:ℝ)+1)) ≤ ∫ t in (0:ℝ)..(k:ℝ), f t := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ, ← integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 (k:ℝ)) (hf.intervalIntegrable (k:ℝ) ((k:ℝ)+1))]
      exact add_le_add ih (hm k)
  have heq : f = fun t : ℝ => Real.exp (-(1/N)*t^2) := by
    funext t
    unfold f
    congr 1
    ring
  have hbound : (∫ t in (0:ℝ)..(k:ℝ), f t) ≤ Real.sqrt (Real.pi*N)/2 := by
    rw [heq, intervalIntegral.integral_of_le (Nat.cast_nonneg _),
      show Real.pi*N = Real.pi/(1/N) by rw [one_div, div_inv_eq_mul],
      ← integral_gaussian_Ioi]
    exact setIntegral_mono_set ((integrable_exp_neg_mul_sq (one_div_pos.2 hN)).integrableOn)
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)) Ioc_subset_Ioi_self.eventuallySubset
  exact hs.trans hbound

private theorem shiftCorrection_rowsum {M k : ℕ} (hk : 2*(k-1) ≤ M)
    {d : ℝ} (hd : 0 ≤ d) (i : Fin k) :
    (∑ j : Fin k, shiftCorrectionMatrix M k d i j) ≤
      (1+Real.sqrt (Real.pi*((M:ℝ)+1)))/2 := by
  classical
  let S := (Finset.univ.erase i).filter (fun j : Fin k => j < i)
  have hsub : S ⊆ Finset.univ.erase i := Finset.filter_subset _ _
  have hrestrict : (∑ j ∈ S, shiftCorrectionMatrix M k d i j) =
      ∑ j ∈ Finset.univ.erase i, shiftCorrectionMatrix M k d i j := by
    apply Finset.sum_subset hsub
    intro j hj hn
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hn' : ¬ j < i := fun hl => hn (Finset.mem_filter.mpr ⟨hj, hl⟩)
    rw [shiftCorrectionMatrix_off_diag d hne.symm]
    simp [shiftTriangular, show ¬j ≤ i from fun hh => hn' (lt_of_le_of_ne hh hne)]
  have hfinite : (∑ j ∈ S, shiftCorrectionMatrix M k d i j) ≤
      ∑ m ∈ Finset.range k, Real.exp (-((m:ℝ)+1)^2/((M:ℝ)+1)) := by
    apply Finset.sum_le_sum_of_injOn (fun j : Fin k => i.val-j.val-1)
    · intro a ha b hb hab
      have ha' : a.val < i.val := (Finset.mem_filter.mp ha).2
      have hb' : b.val < i.val := (Finset.mem_filter.mp hb).2
      change i.val-a.val-1 = i.val-b.val-1 at hab
      exact Fin.ext (by omega)
    · intro m hm
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (by have := i.isLt; omega)
    · intro j hj
      have hji : j.val < i.val := (Finset.mem_filter.mp hj).2
      have hne : i ≠ j := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1.symm
      rw [shiftCorrectionMatrix_off_diag d hne]
      convert shiftTriangular_entry_le_gaussian hk i j using 2
      rw [Nat.cast_sub (show 1 ≤ i.val-j.val by omega), Nat.cast_sub hji.le, Nat.cast_one]
      ring
    · intro m _ _
      positivity
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i), ← hrestrict,
    shiftCorrectionMatrix_diag (by omega)]
  have hg := hfinite.trans (sum_shift_gaussian_le k (show (0:ℝ) < (M:ℝ)+1 by positivity))
  linarith only [hg, hd]

private theorem shiftCorrection_colsum {M k : ℕ} (hk : 2*(k-1) ≤ M)
    {d : ℝ} (hd : 0 ≤ d) (j : Fin k) :
    (∑ i : Fin k, shiftCorrectionMatrix M k d i j) ≤
      (1+Real.sqrt (Real.pi*((M:ℝ)+1)))/2 := by
  classical
  let S := (Finset.univ.erase j).filter (fun i : Fin k => j < i)
  have hsub : S ⊆ Finset.univ.erase j := Finset.filter_subset _ _
  have hrestrict : (∑ i ∈ S, shiftCorrectionMatrix M k d i j) =
      ∑ i ∈ Finset.univ.erase j, shiftCorrectionMatrix M k d i j := by
    apply Finset.sum_subset hsub
    intro i hi hn
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    have hn' : ¬ j < i := fun hl => hn (Finset.mem_filter.mpr ⟨hi, hl⟩)
    rw [shiftCorrectionMatrix_off_diag d hne]
    simp [shiftTriangular, show ¬j ≤ i from fun hh => hn' (lt_of_le_of_ne hh hne.symm)]
  have hfinite : (∑ i ∈ S, shiftCorrectionMatrix M k d i j) ≤
      ∑ m ∈ Finset.range k, Real.exp (-((m:ℝ)+1)^2/((M:ℝ)+1)) := by
    apply Finset.sum_le_sum_of_injOn (fun i : Fin k => i.val-j.val-1)
    · intro a ha b hb hab
      have ha' : j.val < a.val := (Finset.mem_filter.mp ha).2
      have hb' : j.val < b.val := (Finset.mem_filter.mp hb).2
      change a.val-j.val-1 = b.val-j.val-1 at hab
      exact Fin.ext (by omega)
    · intro m hm
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (by have := i.isLt; omega)
    · intro i hi
      have hji : j.val < i.val := (Finset.mem_filter.mp hi).2
      have hne : i ≠ j := (Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1
      rw [shiftCorrectionMatrix_off_diag d hne]
      convert shiftTriangular_entry_le_gaussian hk i j using 2
      rw [Nat.cast_sub (show 1 ≤ i.val-j.val by omega), Nat.cast_sub hji.le, Nat.cast_one]
      ring
    · intro m _ _
      positivity
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j), ← hrestrict,
    shiftCorrectionMatrix_diag (by omega)]
  have hg := hfinite.trans (sum_shift_gaussian_le k (show (0:ℝ) < (M:ℝ)+1 by positivity))
  linarith only [hg, hd]

/-- Both row and column sums give the sharp bound on the correction multiplier. -/
theorem norm_shiftCorrectionMatrix_le {M k : ℕ} (hk : 2*(k-1) ≤ M)
    {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    ‖shiftCorrectionMatrix M k d‖ ≤ (1+Real.sqrt (Real.pi*((M:ℝ)+1)))/2 := by
  exact norm_matrix_le_of_row_col_sum _ (shiftCorrectionMatrix_entry_nonneg (by omega) hd₁)
    (by positivity) (shiftCorrection_rowsum hk hd₀) (shiftCorrection_colsum hk hd₀)

#print axioms sum_shift_gaussian_le
#print axioms norm_shiftCorrectionMatrix_le

end Nuttall
