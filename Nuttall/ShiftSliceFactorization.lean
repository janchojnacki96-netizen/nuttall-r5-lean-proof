import Nuttall.ShiftSliceCentralLower
import Nuttall.ShiftedOrthantConvergence
import Mathlib.GroupTheory.Perm.Fin

namespace Nuttall

open scoped BigOperators

private theorem det_vandermonde_prod_ite {p : ℕ} (w : Fin p → ℝ) :
    (Matrix.vandermonde w).det = ∏ i : Fin p, ∏ j : Fin p, if i < j then w j-w i else 1 := by
  rw [Matrix.det_vandermonde]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

private theorem abs_vandermonde_cons {n : ℕ} (x : ℝ) (v : Fin n → ℝ) :
    |(Matrix.vandermonde (Fin.cons x v)).det| =
      (∏ j, |x-v j|) * |(Matrix.vandermonde v).det| := by
  simp only [det_vandermonde_prod_ite, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    not_lt_zero, ite_false, Fin.succ_pos, ite_true, Fin.succ_lt_succ_iff, one_mul,
    abs_mul, Finset.abs_prod]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => abs_sub_comm _ _)

private theorem abs_vandermonde_insertNth {n : ℕ} (i : Fin (n+1)) (x : ℝ) (v : Fin n → ℝ) :
    |(Matrix.vandermonde (i.insertNth (α := fun _ => ℝ) x v)).det| =
      (∏ j, |x-v j|) * |(Matrix.vandermonde v).det| := by
  let w := i.insertNth (α := fun _ => ℝ) x v
  let σ := i.cycleRange.symm
  have hcons : w ∘ σ = Fin.cons x v := by
    funext j
    exact Fin.insertNth_apply_cycleRange_symm i x v j
  have he : Matrix.vandermonde (w ∘ σ) = (Matrix.vandermonde w).submatrix σ id := by
    ext a b
    simp [Matrix.vandermonde_apply]
  have hsign : |(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ)| = 1 := by
    exact_mod_cast Equiv.Perm.sign_abs σ
  calc
    _ = |(Matrix.vandermonde (w ∘ σ)).det| := by
      rw [he, Matrix.det_permute, abs_mul, hsign, one_mul]
    _ = _ := by rw [hcons, abs_vandermonde_cons]

/-- Signed cofactors of the column corresponding to the free coordinate. -/
noncomputable def shiftSliceCofactor {n : ℕ} (L : ℕ) (i : Fin (n+1))
    (v : Fin n → ℝ) (j : Fin (n+1)) : ℝ :=
  (-1:ℝ)^(j.val+i.val) *
    (Matrix.of (fun (a b : Fin n) =>
      shiftedMoment (L+(j.succAbove a).val-1) (v b))).det

theorem det_shiftedMoment_insertNth {n : ℕ} (L : ℕ) (i : Fin (n+1)) (v : Fin n → ℝ) (x : ℝ) :
    (Matrix.of (fun (a b : Fin (n+1)) =>
      shiftedMoment (L+a.val-1) (i.insertNth (α := fun _ => ℝ) x v b))).det =
      ∑ j, shiftSliceCofactor L i v j * shiftedMoment (L+j.val-1) x := by
  rw [Matrix.det_succ_column _ i]
  apply Finset.sum_congr rfl
  intro j _
  have hM : (Matrix.of (fun (a b : Fin (n+1)) =>
      shiftedMoment (L+a.val-1) (i.insertNth (α := fun _ => ℝ) x v b))).submatrix j.succAbove i.succAbove =
      Matrix.of (fun (a b : Fin n) => shiftedMoment (L+(j.succAbove a).val-1) (v b)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.insertNth_apply_succAbove]
  rw [hM]
  simp only [Matrix.of_apply, Fin.insertNth_apply_same, shiftSliceCofactor]
  ring

/-- All factors independent of the free coordinate factor out as a single
nonnegative constant. This identity also covers coincident frozen nodes. -/
theorem abs_shiftedOrthantIntegrand_insertNth {n : ℕ} (L : ℕ) (i : Fin (n+1))
    (v : Fin n → ℝ) (X x : ℝ) :
    |shiftedOrthantIntegrand X (fun (j _ : Fin (n+1)) =>
      shiftedMoment (L+j.val-1)) (i.insertNth (α := fun _ => ℝ) x v)| =
      (|(Matrix.vandermonde (fun j => Real.exp (4*v j))).det| *
        ∏ j, thetaOrthantWeight X (v j)) * shiftSliceDensity L (shiftSliceCofactor L i v) v X x := by
  have hV : (fun j => Real.exp (4*i.insertNth (α := fun _ => ℝ) x v j)) =
      i.insertNth (α := fun _ => ℝ) (Real.exp (4*x)) (fun j => Real.exp (4*v j)) := by
    apply funext
    rw [i.forall_iff_succAbove]
    simp
  have hW : |∏ j, thetaOrthantWeight X (i.insertNth (α := fun _ => ℝ) x v j)| =
      thetaOrthantWeight X x * ∏ j, thetaOrthantWeight X (v j) := by
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rw [abs_of_nonneg (by unfold thetaOrthantWeight; positivity)]
  unfold shiftedOrthantIntegrand shiftSliceDensity
  rw [abs_mul, abs_mul, det_shiftedMoment_insertNth, hV, abs_vandermonde_insertNth, hW]
  ring

#print axioms abs_shiftedOrthantIntegrand_insertNth

end Nuttall
