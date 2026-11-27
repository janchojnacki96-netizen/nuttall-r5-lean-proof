import Nuttall.PhiRankEightGaussianMatrix
import Nuttall.PhiRankEightShiftNorm
import Mathlib.Tactic.Ring

namespace Nuttall

open scoped Matrix

/-- Sign diagonal of the Gaussian coefficient matrix at the first square. -/
noncomputable def phiRankEightSign (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.diagonal fun i => (-1:ℝ)^i.val

theorem phiRankEightGaussianMatrix_one (p : ℕ) (X : ℝ) :
    phiRankEightGaussianMatrix p X 1 = phiRankEightSign p := by
  ext i j
  simp only [phiRankEightGaussianMatrix, Matrix.of_apply, phiRankEightGaussian_one,
    phiRankEightSign, Matrix.diagonal_apply, Fin.val_inj]

theorem phiRankEightSign_mul_self (p : ℕ) : phiRankEightSign p * phiRankEightSign p = 1 := by
  rw [phiRankEightSign, Matrix.diagonal_mul_diagonal]
  ext i j
  have h : ((-1:ℝ)^i.val)*((-1:ℝ)^i.val) = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  simp [Matrix.diagonal_apply, Matrix.one_apply, h]

theorem phiRankEightSign_mul_shift (p : ℕ) :
    phiRankEightSign p * phiRankEightShift p = -(phiRankEightShift p * phiRankEightSign p) := by
  ext i j
  simp only [phiRankEightSign, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply,
    phiRankEightShift, Matrix.of_apply]
  by_cases h : i.val = j.val+1
  · simp only [h, ite_true, pow_succ]
    ring
  · simp [h]

theorem phiRankEightShift_mul_transpose (p : ℕ) :
    phiRankEightShift p * (phiRankEightShift p).transpose =
      Matrix.diagonal (fun i : Fin p => (i.val:ℝ)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, phiRankEightShift, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : i.val = 0
    · simp [hi]
    · let pred : Fin p := ⟨i.val-1, by have := i.isLt; omega⟩
      rw [Finset.sum_eq_single pred]
      · have hp : i.val = pred.val+1 := by dsimp [pred]; omega
        rw [ite_eq_left hp, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      · intro k _ hk
        have hk' : i.val ≠ k.val+1 := by
          intro he
          apply hk
          apply Fin.ext
          dsimp [pred]
          omega
        simp [hk']
      · simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hi : i.val = k.val+1
    · have hj : j.val ≠ k.val+1 := by
        intro he
        apply hij
        exact Fin.ext (hi.trans he.symm)
      simp [hj]
    · simp [hi]

/-- The first-square block after its sign diagonal has been applied. -/
noncomputable def phiRankEightDominantBlock (p : ℕ) (X : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.diagonal (fun i => 2*X-3-2*(i.val:ℝ)) +
    (2*Real.sqrt X) • (phiRankEightShift p - (phiRankEightShift p).transpose)

theorem phiRankEightDominantBlock_quadratic_le (p : ℕ) (X : ℝ) (x : Fin p → ℝ) :
    (2*X-2*(p:ℝ)-1)*(x ⬝ᵥ x) ≤ x ⬝ᵥ (phiRankEightDominantBlock p X *ᵥ x) := by
  let d (i : Fin p) := 2*X-3-2*(i.val:ℝ)
  have hd : (Matrix.diagonal d *ᵥ x) = fun i => d i*x i := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [phiRankEightDominantBlock, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, Matrix.dotProduct_transpose_mulVec,
    sub_self, smul_zero, add_zero]
  change (2*X-2*(p:ℝ)-1)*(x ⬝ᵥ x) ≤ x ⬝ᵥ (Matrix.diagonal d *ᵥ x)
  rw [hd]
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : (i.val:ℝ)+1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  calc
    _ ≤ d i*(x i*x i) := mul_le_mul_of_nonneg_right (by dsimp [d]; linarith only [hi])
      (mul_self_nonneg _)
    _ = _ := by ring

#print axioms phiRankEightGaussianMatrix_one
#print axioms phiRankEightSign_mul_self
#print axioms phiRankEightSign_mul_shift
#print axioms phiRankEightShift_mul_transpose
#print axioms phiRankEightDominantBlock_quadratic_le

end Nuttall
