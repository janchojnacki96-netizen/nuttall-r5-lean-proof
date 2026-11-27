import Nuttall.WronskianObstruction

namespace Nuttall

open scoped BigOperators

/-- Replace just the top-left entry of a matrix. -/
def replaceMatrixCorner {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (fun i j => if i = 0 ∧ j = 0 then a else A i j)

theorem det_replaceMatrixCorner {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : ℝ) : (replaceMatrixCorner A a).det =
      A.det + (a - A 0 0) * (A.submatrix Fin.succ Fin.succ).det := by
  have hMinor (j : Fin (n+1)) :
      (replaceMatrixCorner A a).submatrix Fin.succ j.succAbove =
        A.submatrix Fin.succ j.succAbove := by
    ext i k
    simp [replaceMatrixCorner, Matrix.submatrix_apply]
  have hTail (j : Fin n) : replaceMatrixCorner A a 0 j.succ = A 0 j.succ := by
    simp [replaceMatrixCorner]
  have hHead : replaceMatrixCorner A a 0 0 = a := by simp [replaceMatrixCorner]
  rw [Matrix.det_succ_row_zero (replaceMatrixCorner A a), Matrix.det_succ_row_zero A]
  simp only [hMinor, Fin.sum_univ_succ, hTail, hHead, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  ring

/-- The rank-eight test can use a lower bound on the zeroth jet given a
nonpositive cofactor and a negative determinant at the substituted value. -/
theorem two_le_kernelIntegrationOrder_of_psiOne_corner {t a : ℝ} (ht : 0 ≤ t)
    (ha : a ≤ psi 1 t)
    (hcof : ((Matrix.of (fun (i j : Fin 8) => iteratedDeriv (i.val + j.val) (psi 1) t)).submatrix
      Fin.succ Fin.succ).det ≤ 0)
    (hdet : (replaceMatrixCorner
      (Matrix.of (fun (i j : Fin 8) => iteratedDeriv (i.val + j.val) (psi 1) t)) a).det < 0) :
    2 ≤ kernelIntegrationOrder 8 := by
  let A := Matrix.of (fun (i j : Fin 8) => iteratedDeriv (i.val+j.val) (psi 1) t)
  have h₀ : A 0 0 = psi 1 t := by simp [A]
  have hm : 0 ≤ (a - A 0 0) * (A.submatrix Fin.succ Fin.succ).det := by
    apply mul_nonneg_of_nonpos_of_nonpos _ hcof
    simpa only [sub_nonpos, h₀] using ha
  have hn : A.det < 0 := by
    rw [det_replaceMatrixCorner A a] at hdet
    linarith only [hdet, hm]
  exact kernelIntegrationOrder_succ_le_of_negative_wronskian (m := 1) (p := 8) (t := t)
    (by decide) le_rfl ht (by norm_num [kernelMinorSign]; exact hn)

#print axioms two_le_kernelIntegrationOrder_of_psiOne_corner

end Nuttall
