import Nuttall.PsiDerivatives

namespace Nuttall

open scoped BigOperators

private theorem sum_fin_indices (p : ℕ) :
    (∑ i : Fin p, i.val) = p * (p-1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

theorem sign_revPerm (p : ℕ) :
    Equiv.Perm.sign (@Fin.revPerm p) = (-1 : ℤˣ)^(p * (p-1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  calc
    _ = ∏ j : Fin p, (-1 : ℤˣ)^j.val := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← Fin.card_Iio (b := j), ← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro i hi
      have hij := Finset.mem_Iio.mp hi
      simp only [Fin.revPerm_apply, Fin.rev_lt_rev, if_neg (not_lt_of_ge hij.le)]
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, sum_fin_indices]

private theorem det_remove_entry_signs {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    (Matrix.of (fun (i j : Fin p) => (-1 : ℝ)^(i.val+j.val) * A i j)).det = A.det := by
  let v : Fin p → ℝ := fun i => (-1)^i.val
  have hmat :
      Matrix.of (fun (i j : Fin p) => (-1 : ℝ)^(i.val+j.val) * A i j) =
      Matrix.of (fun (i j : Fin p) =>
        v j * (Matrix.of (fun (k l : Fin p) => v k * A k l)) i j) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.of_apply, v, pow_add]
    ring
  rw [hmat, Matrix.det_mul_row, Matrix.det_mul_column]
  have hv : (∏ i, v i) * (∏ i, v i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    dsimp [v]
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hv, one_mul]

/-- Signed Wronskian in the upper-tail determinant form used in Section 4.1.
The size condition ensures that natural subtraction agrees with the displayed
integer indices. -/
theorem signed_wronskian_psi_eq_tail_det {p m : ℕ}
    (hm : 2*(p-1) ≤ m) (t : ℝ) :
    (-1 : ℝ)^(p*(p-1)/2) * wronskian (psi m) p t =
      (Matrix.of (fun (i j : Fin p) => psi (m-(p-1)+i.val-j.val) t)).det := by
  let A : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of (fun (i j : Fin p) => psi (m-(i.val+j.val)) t)
  have hw : wronskian (psi m) p t = A.det := by
    rw [wronskian_psi_eq_det hm]
    exact det_remove_entry_signs A
  have hrev : A.submatrix Fin.revPerm id =
      Matrix.of (fun (i j : Fin p) => psi (m-(p-1)+i.val-j.val) t) := by
    apply Matrix.ext
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    have hindex : m-((i.rev).val+j.val) = m-(p-1)+i.val-j.val := by
      rw [Fin.val_rev]
      omega
    simp only [Matrix.submatrix_apply, Fin.revPerm_apply, id_eq, Matrix.of_apply, A, hindex]
  have hsign : (((Equiv.Perm.sign (@Fin.revPerm p) : ℤˣ) : ℤ) : ℝ) =
      (-1 : ℝ)^(p*(p-1)/2) := by
    rw [sign_revPerm]
    norm_num [Units.val_pow_eq_pow_val]
  rw [hw, ← hrev, Matrix.det_permute, hsign]

#print axioms signed_wronskian_psi_eq_tail_det

end Nuttall
