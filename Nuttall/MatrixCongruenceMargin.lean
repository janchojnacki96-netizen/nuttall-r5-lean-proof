import Nuttall.MatrixRowMargin
import Nuttall.SignedKernelCriterion
import Mathlib.LinearAlgebra.Matrix.Block

namespace Nuttall

open scoped BigOperators

/-- The sign of a determinant agrees with that of the sign diagonal whenever
their entrywise difference has every absolute row sum less than one. -/
theorem signed_det_pos_of_row_margin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (s : ι → ℝ) (hs : ∀ i, |s i| = 1)
    (hmargin : ∀ i, (∑ j, |B i j - Matrix.diagonal s i j|) < 1) :
    0 < (∏ i, s i) * B.det := by
  have hsq (i : ι) : s i * s i = 1 := by
    have h := congrArg (fun x : ℝ => x * x) (hs i)
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _), mul_one] at h
    exact h
  have hentry (i j : ι) :
      ((Matrix.diagonal s * B) i j - Matrix.diagonal (fun _ => (1:ℝ)) i j) =
        s i * (B i j - Matrix.diagonal s i j) := by
    rw [Matrix.diagonal_mul, mul_sub]
    by_cases hij : i = j
    · subst j
      simp [hsq]
    · simp [hij]
  have h := det_pos_of_row_diagonal_margin (Matrix.diagonal s * B) (fun _ => 1)
    (fun _ => zero_lt_one) (fun i => by simpa only [hentry, abs_mul, hs, one_mul] using hmargin i)
  rwa [Matrix.det_mul, Matrix.det_diagonal] at h

private theorem sum_castLE_eq_of_zero {p n : ℕ} (hp : p ≤ n) (f : Fin n → ℝ)
    (hz : ∀ j : Fin n, p ≤ j.val → f j = 0) :
    (∑ j : Fin p, f (Fin.castLE hp j)) = ∑ j : Fin n, f j := by
  let e := Fin.castLE hp
  calc
    _ = ∑ j ∈ Finset.univ.image e, f j :=
      (Finset.sum_image (fun i _ j _ hij => Fin.castLE_injective hp hij)).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hn
      apply hz
      by_contra! hj
      apply hn
      exact Finset.mem_image.mpr ⟨⟨j.val, hj⟩, Finset.mem_univ _, Fin.ext rfl⟩

private theorem submatrix_castLE_congruence {p n : ℕ} (hp : p ≤ n)
    (A U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsLowerTriangular) :
    (U * A * U.transpose).submatrix (Fin.castLE hp) (Fin.castLE hp) =
      (U.submatrix (Fin.castLE hp) (Fin.castLE hp)) *
      (A.submatrix (Fin.castLE hp) (Fin.castLE hp)) *
      (U.submatrix (Fin.castLE hp) (Fin.castLE hp)).transpose := by
  let e := Fin.castLE hp
  have hleft : (U * A).submatrix e e = U.submatrix e e * A.submatrix e e := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine sum_castLE_eq_of_zero hp (fun k => U (e i) k * A k (e j)) ?_
    intro k hk
    have hz : U (e i) k = 0 :=
      hU (i := e i) (j := k) (Fin.lt_def.mpr (i.isLt.trans_le hk))
    rw [hz, zero_mul]
  have hright : (U * A * U.transpose).submatrix e e =
      (U * A).submatrix e e * (U.submatrix e e).transpose := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
    symm
    refine sum_castLE_eq_of_zero hp (fun k => (U * A) (e i) k * U (e j) k) ?_
    intro k hk
    have hz : U (e j) k = 0 :=
      hU (i := e j) (j := k) (Fin.lt_def.mpr (j.isLt.trans_le hk))
    rw [hz, mul_zero]
  exact hright.trans (by rw [hleft])

/-- A single row-margin certificate after a lower triangular congruence
fixes the signs of every leading principal determinant. -/
theorem signed_leading_det_pos_of_triangular_congruence {p n : ℕ} (hp : p ≤ n)
    (A U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsLowerTriangular)
    (hdiag : ∀ i, U i i ≠ 0)
    (hmargin : ∀ i, (∑ j, |(U * A * U.transpose) i j -
        Matrix.diagonal (fun k : Fin n => (-1 : ℝ)^k.val) i j|) < 1) :
    0 < kernelMinorSign p * (A.submatrix (Fin.castLE hp) (Fin.castLE hp)).det := by
  let e := Fin.castLE hp
  let B := U * A * U.transpose
  let C := U.submatrix e e
  have htri : C.IsLowerTriangular := by
    intro i j hij
    exact hU (show e i < e j from Fin.lt_def.mpr hij)
  have hC : C.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular C htri]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag (e i))
  have hsub (i : Fin p) : (∑ j : Fin p, |B (e i) (e j) -
      Matrix.diagonal (fun k : Fin p => (-1 : ℝ)^k.val) i j|) < 1 := by
    have hentry (j : Fin p) :
        Matrix.diagonal (fun k : Fin n => (-1 : ℝ)^k.val) (e i) (e j) =
          Matrix.diagonal (fun k : Fin p => (-1 : ℝ)^k.val) i j := by
      by_cases hij : i = j
      · subst j
        simp [e]
      · have he : e i ≠ e j := fun h => hij (Fin.castLE_injective hp h)
        simp [hij, he]
    simp_rw [← hentry]
    refine lt_of_le_of_lt ?_ (hmargin (e i))
    let q (k : Fin n) := |B (e i) k - Matrix.diagonal (fun j : Fin n => (-1 : ℝ)^j.val) (e i) k|
    change (∑ j : Fin p, q (e j)) ≤ ∑ k : Fin n, q k
    calc
      _ = ∑ k ∈ Finset.univ.image e, q k :=
        (Finset.sum_image (f := q) (Fin.castLE_injective hp).injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => abs_nonneg _)
  have hsign : (∏ i : Fin p, (-1 : ℝ)^i.val) = kernelMinorSign p := by
    have hsum : (∑ i : Fin p, i.val) = p * (p - 1) / 2 :=
      (Fin.sum_univ_eq_sum_range (fun x : ℕ => x) p).trans (Finset.sum_range_id p)
    rw [Finset.prod_pow_eq_pow_sum, hsum, kernelMinorSign]
  have h := signed_det_pos_of_row_margin (B.submatrix e e) (fun i => (-1 : ℝ)^i.val)
    (fun i => by rw [abs_pow, abs_neg, abs_one, one_pow])
    (by simpa only [Matrix.submatrix_apply] using hsub)
  rw [hsign, submatrix_castLE_congruence hp A U hU, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose] at h
  have hsquare : 0 < C.det ^ 2 := sq_pos_of_ne_zero hC
  have hprod : 0 < C.det ^ 2 * (kernelMinorSign p * (A.submatrix e e).det) := by
    convert h using 1
    change _ = kernelMinorSign p * (C.det * (A.submatrix e e).det * C.det)
    ring
  exact (mul_pos_iff_of_pos_left hsquare).mp hprod

#print axioms signed_leading_det_pos_of_triangular_congruence

end Nuttall
