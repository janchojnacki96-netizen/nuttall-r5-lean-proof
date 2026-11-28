import Nuttall.ShiftFirstKnotCore
import Nuttall.ShiftCorrection
import Mathlib.Data.Matrix.Basis

namespace Nuttall

private theorem shiftCorrectionMatrix_one_eq_zero_of_le {l : ℕ} (hl : 1 ≤ l)
    (i j : Fin (l+1)) (h : i ≤ j) : shiftCorrectionMatrix (2*l-1) (l+1) 1 i j = 0 := by
  by_cases he : i = j
  · subst j
    have hi : i.val ≤ 2*l-1 := by have := i.isLt; omega
    have hp : ((2*l-1).choose i.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
    simp [shiftCorrectionMatrix, shiftTriangular, hp]
  · have hj : ¬ j ≤ i := fun h' => he (le_antisymm h h')
    simp [shiftCorrectionMatrix, shiftTriangular, hj, he]

private theorem shiftCorrectionMatrix_one_last_prev {l : ℕ} (hl : 1 ≤ l) :
    shiftCorrectionMatrix (2*l-1) (l+1) 1 (Fin.last l) ⟨l-1, by omega⟩ = 1 := by
  let j : Fin (l+1) := ⟨l-1, by omega⟩
  have hj : j.val = l-1 := rfl
  have hne : Fin.last l ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, hj] at this
    omega
  have hle : j ≤ Fin.last l := show l-1 ≤ l by omega
  have hchoose : (2*l-1).choose (l-1) = (2*l-1).choose l := by
    simpa only [show 2*l-1-l = l-1 by omega] using
      (Nat.choose_symm (show l ≤ 2*l-1 by omega))
  have hp : ((2*l-1).choose l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show l ≤ 2*l-1 by omega)).ne'
  change shiftCorrectionMatrix (2*l-1) (l+1) 1 (Fin.last l) j = 1
  simp [shiftCorrectionMatrix, shiftTriangular, hle, hne, hj, hchoose, hp]

private theorem shiftCorrectionMatrix_one_mul_shiftCore_one {l : ℕ} (hl : 1 ≤ l) :
    shiftCorrectionMatrix (2*l-1) (l+1) 1 * shiftCore (2*l-1) (l+1) 1 =
      Matrix.single (Fin.last l) (Fin.last l) (1:ℝ) := by
  let j₀ : Fin (l+1) := ⟨l-1, by omega⟩
  have hj₀ : j₀.val = l-1 := rfl
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single j₀]
  · by_cases hi : i = Fin.last l
    · subst i
      rw [shiftCorrectionMatrix_one_last_prev hl, one_mul]
      by_cases hj : j = Fin.last l
      · subst j
        rw [Matrix.single_apply_same]
        have hsum : j₀.val + (Fin.last l).val = 2*l-1 := by
          simp only [hj₀, Fin.val_last]
          omega
        exact shiftCore_one_eq_one_of_add_eq j₀ (Fin.last l) hsum
      · have hj' : j.val ≠ l := fun h => hj (Fin.ext h)
        have hjlt := j.isLt
        rw [shiftCore_one_eq_zero_of_add_lt j₀ j (by omega)]
        simp [Ne.symm hj]
    · have hi' : i.val ≠ l := fun h => hi (Fin.ext h)
      have hilt := i.isLt
      have hle : i ≤ j₀ := show i.val ≤ j₀.val by omega
      rw [shiftCorrectionMatrix_one_eq_zero_of_le hl i j₀ hle, zero_mul,
        Matrix.single_apply_of_row_ne (Ne.symm hi)]
  · intro k _ hk
    by_cases he : k.val = l
    · have hil := i.isLt
      have hle : i ≤ k := show i.val ≤ k.val by omega
      rw [shiftCorrectionMatrix_one_eq_zero_of_le hl i k hle, zero_mul]
    · have hk' : k.val ≠ l-1 := fun h => hk (Fin.ext (h.trans hj₀.symm))
      have hkl := k.isLt
      have hjl := j.isLt
      rw [shiftCore_one_eq_zero_of_add_lt k j (by omega), mul_zero]
  · intro h
    exact (h (Finset.mem_univ j₀)).elim

/-- At full shift the symmetric correction contributes only two to
the last diagonal entry of the block. -/
theorem shiftCore_one_firstKnot_correction {l : ℕ} (hl : 1 ≤ l) :
    let C := shiftCore (2*l-1) (l+1) 1
    let V := shiftCorrectionMatrix (2*l-1) (l+1) 1
    V*C + C*V.transpose = Matrix.single (Fin.last l) (Fin.last l) (2:ℝ) := by
  let C := shiftCore (2*l-1) (l+1) 1
  let V := shiftCorrectionMatrix (2*l-1) (l+1) 1
  let S := Matrix.single (Fin.last l) (Fin.last l) (1:ℝ)
  change V*C + C*V.transpose = _
  have hC : C.transpose = C := by
    ext i j
    rw [Matrix.transpose_apply]
    dsimp only [C]
    rw [shiftCore_one_firstKnot_entries hl j i, shiftCore_one_firstKnot_entries hl i j]
    simp only [and_comm, Nat.add_comm j.val i.val]
  have hS : S.transpose = S := by
    ext i j
    simp only [S, Matrix.transpose_apply, Matrix.single_apply, and_comm]
  have hleft : V*C = S := shiftCorrectionMatrix_one_mul_shiftCore_one hl
  have hright : C*V.transpose = S := by
    have h := congrArg Matrix.transpose hleft
    simpa only [Matrix.transpose_mul, hC, hS] using h
  rw [hleft, hright]
  ext i j
  simp only [S, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> norm_num

#print axioms shiftCore_one_firstKnot_correction

end Nuttall
