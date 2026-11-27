import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Nuttall

open scoped Matrix.Norms.Operator NNReal

/-- Multiplication by the coordinate in the normalized monomial basis. -/
noncomputable def phiRankEightShift (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => if i.val = j.val+1 then Real.sqrt (i.val:ℝ) else 0

private theorem norm_le_three_of_single_entry {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (entry : Fin p → Fin p → Prop) [DecidableRel entry]
    (hA : ∀ i j, |A i j| ≤ if entry i j then 3 else 0)
    (hunique : ∀ i j k, entry i j → entry i k → j = k) :
    ‖A‖ ≤ 3 := by
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup fun i : Fin p => ∑ j : Fin p, ‖A i j‖₊ : ℝ≥0):ℝ) ≤ ((3:ℝ≥0):ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  push_cast
  simp only [Real.norm_eq_abs]
  have hcard : (Finset.univ.filter (entry i)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    exact hunique i j k (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
  calc
    _ ≤ ∑ j : Fin p, if entry i j then (3:ℝ) else 0 := Finset.sum_le_sum (fun j _ => hA i j)
    _ = ((Finset.univ.filter (entry i)).card:ℝ)*3 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have h : ((Finset.univ.filter (entry i)).card:ℝ) ≤ 1 := by exact_mod_cast hcard
      linarith only [h]

private theorem rankEight_sqrt_index_le {p : ℕ} (hp : p ≤ 8) (i : Fin p) :
    Real.sqrt (i.val:ℝ) ≤ 3 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by
    have h : i.val ≤ 8 := i.isLt.le.trans hp
    have h' : (i.val:ℝ) ≤ 8 := by exact_mod_cast h
    linarith only [h']⟩

theorem phiRankEightShift_norm_le {p : ℕ} (hp : p ≤ 8) : ‖phiRankEightShift p‖ ≤ 3 := by
  apply norm_le_three_of_single_entry _ (fun i j => i.val = j.val+1)
  · intro i j
    simp only [phiRankEightShift, Matrix.of_apply]
    split
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact rankEight_sqrt_index_le hp i
    · simp
  · intro i j k hj hk
    exact Fin.ext (by omega)

theorem phiRankEightShift_transpose_norm_le {p : ℕ} (hp : p ≤ 8) :
    ‖(phiRankEightShift p).transpose‖ ≤ 3 := by
  apply norm_le_three_of_single_entry _ (fun i j => j.val = i.val+1)
  · intro i j
    simp only [Matrix.transpose_apply, phiRankEightShift, Matrix.of_apply]
    split
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact rankEight_sqrt_index_le hp j
    · simp
  · intro i j k hj hk
    exact Fin.ext (by omega)

/-- Coefficient matrix of multiplication by 1+u/√X. -/
noncomputable def phiRankEightCongruenceFactor (p : ℕ) (X : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  1 + (Real.sqrt X)⁻¹ • phiRankEightShift p

private theorem rankEightCongruenceFactor_norm_aux {p : ℕ} (hp : 0 < p) {X : ℝ}
    (hX : 16 ≤ X) (S : Matrix (Fin p) (Fin p) ℝ) (hS : ‖S‖ ≤ 3) :
    ‖1 + (Real.sqrt X)⁻¹ • S‖ ≤ 7/4 := by
  let : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  have hroot : (4:ℝ) ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) (by linarith)).2 (by
    norm_num
    exact hX)
  have hinv := inv_anti₀ (by norm_num : (0:ℝ) < 4) hroot
  have hinv₀ : 0 ≤ (Real.sqrt X)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg X)
  calc
    _ ≤ ‖(1:Matrix (Fin p) (Fin p) ℝ)‖ + ‖(Real.sqrt X)⁻¹ • S‖ := norm_add_le _ _
    _ = 1 + (Real.sqrt X)⁻¹ * ‖S‖ := by rw [norm_one, norm_smul, Real.norm_of_nonneg hinv₀]
    _ ≤ 1 + (4:ℝ)⁻¹*3 :=
      add_le_add le_rfl (mul_le_mul hinv hS (norm_nonneg _) (by norm_num))
    _ = _ := by norm_num

theorem phiRankEightCongruenceFactor_norm_le {p : ℕ} (hp₀ : 0 < p) (hp : p ≤ 8)
    {X : ℝ} (hX : 16 ≤ X) : ‖phiRankEightCongruenceFactor p X‖ ≤ 7/4 :=
  rankEightCongruenceFactor_norm_aux hp₀ hX _ (phiRankEightShift_norm_le hp)

theorem phiRankEightCongruenceFactor_transpose_norm_le {p : ℕ} (hp₀ : 0 < p) (hp : p ≤ 8)
    {X : ℝ} (hX : 16 ≤ X) : ‖(phiRankEightCongruenceFactor p X).transpose‖ ≤ 7/4 := by
  simpa only [phiRankEightCongruenceFactor, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_smul] using
    rankEightCongruenceFactor_norm_aux hp₀ hX _ (phiRankEightShift_transpose_norm_le hp)

#print axioms phiRankEightShift_norm_le
#print axioms phiRankEightShift_transpose_norm_le
#print axioms phiRankEightCongruenceFactor_norm_le
#print axioms phiRankEightCongruenceFactor_transpose_norm_le

end Nuttall
