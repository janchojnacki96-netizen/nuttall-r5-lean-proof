import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Order.IntermediateValue

namespace Nuttall

open scoped Matrix.Norms.Operator

/-- A positive diagonal with a strict row-sum margin fixes the determinant sign. -/
theorem det_pos_of_row_diagonal_margin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (h : ∀ i, (∑ j, |A i j - Matrix.diagonal d i j|) < d i) : 0 < A.det := by
  let B := Matrix.diagonal (fun i => (d i)⁻¹) * A
  have hentry (i j : ι) : (B-1) i j = (d i)⁻¹ * (A i j - Matrix.diagonal d i j) := by
    simp only [B, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.one_apply, Matrix.diagonal_apply,
      mul_sub]
    split_ifs with h'
    · simp [(hd i).ne']
    · simp
  have hN : ‖B-1‖ < 1 := by
    rw [Matrix.linfty_opNorm_def]
    change ((Finset.univ.sup fun i : ι => ∑ j : ι, ‖(B-1) i j‖₊ : ℝ≥0):ℝ) < ((1:ℝ≥0):ℝ)
    rw [NNReal.coe_lt_coe, Finset.sup_lt_iff (show (0:ℝ≥0) < 1 by norm_num)]
    intro i _
    apply NNReal.coe_lt_coe.mp
    push_cast
    simp only [Real.norm_eq_abs, hentry, abs_mul,
      abs_of_pos (inv_pos.mpr (hd i)), ← Finset.mul_sum]
    simpa only [inv_mul_cancel₀ (hd i).ne'] using
      mul_lt_mul_of_pos_left (h i) (inv_pos.mpr (hd i))
  let f (t : ℝ) := (1 + t • (B-1)).det
  have hf : Continuous f := by apply Continuous.matrix_det; fun_prop
  have hzero : f 0 = 1 := by simp [f]
  have hone : f 1 = B.det := by simp [f, add_comm (1 : Matrix ι ι ℝ)]
  have hno (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : f t ≠ 0 := by
    have hn : ‖-(t • (B-1))‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hN
    have hu := IsUnit.one_sub_of_norm_lt_one hn
    have he := (Matrix.isUnit_iff_isUnit_det _).1 hu
    simpa only [sub_neg_eq_add, f] using he.ne_zero
  have hb : 0 < B.det := by
    by_contra! hn
    have hm : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := by simp [hzero, hone, hn]
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num) hf.continuousOn hm
    exact hno t ht he
  have hD : 0 < ∏ i : ι, (d i)⁻¹ := Finset.prod_pos fun i _ => inv_pos.mpr (hd i)
  rw [show B = Matrix.diagonal (fun i => (d i)⁻¹) * A from rfl, Matrix.det_mul, Matrix.det_diagonal] at hb
  exact (mul_pos_iff_of_pos_left hD).mp hb

#print axioms det_pos_of_row_diagonal_margin

end Nuttall
