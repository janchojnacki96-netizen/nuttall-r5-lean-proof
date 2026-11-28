import Nuttall.MatrixSchurBound
import Nuttall.ShiftTriangularDecay

namespace Nuttall

open scoped BigOperators Matrix.Norms.L2Operator

private theorem firstKnot_choose_mono {l a b : ℕ} (hab : a ≤ b) (hb : b ≤ l) :
    (2*l-1).choose a ≤ (2*l-1).choose b := by
  induction hab with
  | refl => exact le_rfl
  | @step b hab ih =>
    refine (ih (by omega)).trans ?_
    by_cases h : b < (2*l-1)/2
    · exact Nat.choose_le_succ_of_lt_half_left h
    · have he : 2*l-1-(b+1) = b := by omega
      exact (by
        simpa only [he] using (Nat.choose_symm (show b+1 ≤ 2*l-1 by omega)).le)

private theorem firstKnot_shiftTriangular_bounds {l : ℕ} (hl : 1 ≤ l)
    (i j : Fin (l+1)) : 0 ≤ shiftTriangular (2*l-1) (l+1) i j ∧
    shiftTriangular (2*l-1) (l+1) i j ≤ 1 := by
  by_cases hj : j ≤ i
  · have hi : i.val ≤ l := by have := i.isLt; omega
    have hchoose : ((2*l-1).choose j.val : ℝ) ≤ (2*l-1).choose i.val := by
      exact_mod_cast firstKnot_choose_mono hj hi
    have hpos : 0 < ((2*l-1).choose i.val : ℝ) := by
      exact_mod_cast Nat.choose_pos (show i.val ≤ 2*l-1 by omega)
    simp only [shiftTriangular, Matrix.of_apply, ite_eq_left hj]
    exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_iff).2
      ⟨by norm_num, by simpa using (div_le_one hpos).2 hchoose⟩⟩
  · simp [shiftTriangular, hj]

private theorem firstKnot_sum_le_of_half_entry {l : ℕ} (i : Fin (l+1))
    (f : Fin (l+1) → ℝ) (hhalf : f i = 1/2) (h : ∀ j ≠ i, f j ≤ 1) :
    ∑ j, f j ≤ (l:ℝ) + 1/2 := by
  classical
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i), hhalf]
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact h j (Finset.mem_erase.mp hj).1
    _ = l := by simp

/-- The unshifted triangular correction has the operator bound used
for the left-hand limit in Theorem 6.3. -/
theorem norm_firstKnot_unshifted_correction_le {l : ℕ} (hl : 1 ≤ l) :
    ‖shiftCorrectionMatrix (2*l-1) (l+1) 0‖ ≤ (l:ℝ)+1/2 := by
  let V := shiftCorrectionMatrix (2*l-1) (l+1) 0
  have hdiag (i : Fin (l+1)) : V i i = 1/2 := by
    simpa [V] using shiftCorrectionMatrix_diag (M := 2*l-1) (k := l+1) (by omega) 0 i
  have hoff (i j : Fin (l+1)) (h : i ≠ j) : 0 ≤ V i j ∧ V i j ≤ 1 := by
    dsimp [V]
    rw [shiftCorrectionMatrix_off_diag 0 h]
    exact firstKnot_shiftTriangular_bounds hl i j
  refine norm_matrix_le_of_row_col_sum V ?_ (by positivity) ?_ ?_
  · intro i j
    by_cases h : i = j
    · subst j
      rw [hdiag]
      norm_num
    · exact (hoff i j h).1
  · intro i
    exact firstKnot_sum_le_of_half_entry i (V i) (hdiag i)
      (fun j hj => (hoff i j (Ne.symm hj)).2)
  · intro j
    exact firstKnot_sum_le_of_half_entry j (fun i => V i j) (hdiag j)
      (fun i hi => (hoff i j hi).2)

/-- At the first knot the unshifted part is within one half of the sign
matrix whenever the coordinate is at most three eighths. -/
theorem norm_firstKnot_unshifted_perturbation_lt_half {l : ℕ} (hl : 2 ≤ l)
    {u : ℝ} (hu : 0 ≤ u) (hu₃ : u ≤ 3/8) :
    let V := shiftCorrectionMatrix (2*l-1) (l+1) 0
    let J := shiftSignMatrix (l+1)
    ‖(u/(2*(l:ℝ))) • (V*J+J*V.transpose)‖ < 1/2 := by
  let V := shiftCorrectionMatrix (2*l-1) (l+1) 0
  let J := shiftSignMatrix (l+1)
  let q := u/(2*(l:ℝ))
  change ‖q • (V*J+J*V.transpose)‖ < 1/2
  have hJ : ‖J‖ ≤ 1 := by
    change ‖Matrix.diagonal (fun i : Fin (l+1) => (-1:ℝ)^i.val)‖ ≤ 1
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by simp)
  have hV : ‖V‖ ≤ (l:ℝ)+1/2 := norm_firstKnot_unshifted_correction_le (by omega)
  have ht : ‖V.transpose‖ = ‖V‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  have hlr : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hp : 0 < 2*(l:ℝ) := by linarith
  have hq : 0 ≤ q := div_nonneg hu hp.le
  rw [norm_smul, Real.norm_of_nonneg hq]
  calc
    _ ≤ q * (‖V*J‖ + ‖J*V.transpose‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hq
    _ ≤ q * (‖V‖*‖J‖ + ‖J‖*‖V.transpose‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)) hq
    _ ≤ q * (2*(l:ℝ)+1) := by
      rw [ht, mul_comm ‖J‖]
      apply mul_le_mul_of_nonneg_left _ hq
      have hVJ := (mul_le_of_le_one_right (norm_nonneg V) hJ).trans hV
      linarith only [hVJ]
    _ = u*(2*(l:ℝ)+1)/(2*(l:ℝ)) := by dsimp [q]; ring
    _ ≤ (3/8)*(2*(l:ℝ)+1)/(2*(l:ℝ)) := by gcongr
    _ < 1/2 := (div_lt_iff₀ hp).2 (by linarith)

/-- An inverse of a perturbation of an isometry is bounded by two
when the perturbation has norm at most one half. -/
theorem firstKnot_inverse_norm_le_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J B inverse : E →L[ℝ] E) (hJ : ∀ x, ‖J x‖ = ‖x‖)
    (hB : ∀ x, B (inverse x) = x) (hclose : ‖B-J‖ ≤ 1/2) :
    ‖inverse‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have he : J (inverse x) = x - (B-J) (inverse x) := by
    rw [sub_apply, hB]
    abel
  have h₁ : ‖inverse x‖ ≤ ‖x‖ + ‖(B-J) (inverse x)‖ := by
    rw [← hJ (inverse x), he]
    exact norm_sub_le _ _
  have h₂ := ((B-J).le_opNorm (inverse x)).trans
    (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  linarith

/-- The two norm bounds in Theorem 6.3 force a negative Schur complement
once the last diagonal entry is below minus three halves. -/
theorem firstKnot_schur_neg_of_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : E) (T : E →L[ℝ] E) {c : ℝ} (hc : c < -(3/2))
    (hb : ‖b‖ < Real.sqrt 3 / 2) (hT : ‖T‖ ≤ 2) :
    c - inner ℝ b (T b) < 0 := by
  have hs : (Real.sqrt 3 / 2)^2 = (3:ℝ)/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hsq := (sq_lt_sq₀ (norm_nonneg b) (by positivity : 0 ≤ Real.sqrt 3 / 2)).2 hb
  have hval : |inner ℝ b (T b)| < 3/2 := calc
    _ ≤ ‖b‖*‖T b‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖b‖*(‖T‖*‖b‖) := mul_le_mul_of_nonneg_left (T.le_opNorm b) (norm_nonneg _)
    _ = ‖T‖ * ‖b‖^2 := by ring
    _ ≤ 2 * ‖b‖^2 := mul_le_mul_of_nonneg_right hT (sq_nonneg _)
    _ < 3/2 := by linarith only [hs, hsq]
  linarith [(abs_lt.mp hval).1]

#print axioms firstKnot_inverse_norm_le_two
#print axioms firstKnot_schur_neg_of_bounds
#print axioms norm_firstKnot_unshifted_correction_le
#print axioms norm_firstKnot_unshifted_perturbation_lt_half

end Nuttall
