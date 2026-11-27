import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Calculus.Taylor

namespace Nuttall

open Function
open scoped BigOperators

/-- Newton's triangular matrix recovers equally spaced values from
the forward differences at the first point. -/
private def newtonMatrix (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of (fun i j => (i.val.choose j.val : ℝ))

private theorem det_newtonMatrix (p : ℕ) : (newtonMatrix p).det = 1 := by
  have ht : (newtonMatrix p).IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := hij
    simp [newtonMatrix, Nat.choose_eq_zero_of_lt hij']
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp [newtonMatrix]

private theorem newton_sum {p : ℕ} (i : Fin p) (h t : ℝ) (f : ℝ → ℝ) :
    (∑ j : Fin p, newtonMatrix p i j * (fwdDiff h)^[j.val] f t) = f (t+i.val • h) := by
  simp only [newtonMatrix, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => (i.val.choose j:ℝ) * (fwdDiff h)^[j] f t)]
  have hs : Finset.range (i.val+1) ⊆ Finset.range p :=
    Finset.range_mono (Nat.succ_le_of_lt i.isLt)
  rw [← Finset.sum_subset hs]
  · simpa only [nsmul_eq_mul] using (shift_eq_sum_fwdDiff_iter h f i.val t).symm
  · intro j _ hj
    have hij : i.val < j := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj
    simp [Nat.choose_eq_zero_of_lt hij]

/-- Taking all row and column forward differences preserves the determinant
of the addition kernel on an equally spaced grid. -/
theorem det_kernelGrid_eq_det_forwardDiff (p : ℕ) (f : ℝ → ℝ) (t h : ℝ) :
    (Matrix.of (fun (i j : Fin p) => f (t+i.val • h+j.val • h))).det =
      (Matrix.of (fun (i j : Fin p) => (fwdDiff h)^[i.val+j.val] f t)).det := by
  let P := newtonMatrix p
  let D := Matrix.of (fun (i j : Fin p) => (fwdDiff h)^[i.val+j.val] f t)
  have hfirst (i j : Fin p) : (P*D) i j = (fwdDiff h)^[j.val] f (t+i.val • h) := by
    rw [Matrix.mul_apply]
    simpa only [P,D, Matrix.of_apply, Function.iterate_add_apply] using
      newton_sum i h t ((fwdDiff h)^[j.val] f)
  have he : Matrix.of (fun (i j : Fin p) => f (t+i.val • h+j.val • h)) =
      P*D*P.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.transpose_apply, hfirst]
    simpa only [P, mul_comm] using (newton_sum j h (t+i.val • h) f).symm
  rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_newtonMatrix p,
    one_mul, mul_one]

/-- The scale removed from the determinant when each matrix entry is
divided by the power corresponding to its derivative order. -/
theorem det_forwardDiff_eq_scaled (p : ℕ) (f : ℝ → ℝ) (t : ℝ) {h : ℝ} (hh : h ≠ 0) :
      (Matrix.of (fun (i j : Fin p) => (fwdDiff h)^[i.val+j.val] f t)).det =
      ((∏ i : Fin p, h^i.val)^2) *
      (Matrix.of (fun (i j : Fin p) => ((fwdDiff h)^[i.val+j.val] f t) / h^(i.val+j.val))).det := by
  let A := Matrix.of (fun (i j : Fin p) => ((fwdDiff h)^[i.val+j.val] f t) / h^(i.val+j.val))
  let B := Matrix.of (fun (i j : Fin p) => h^j.val * A i j)
  have he : Matrix.of (fun (i j : Fin p) => (fwdDiff h)^[i.val+j.val] f t) =
      Matrix.of (fun (i j : Fin p) => h^i.val * B i j) := by
    ext i j
    simp only [A,B, Matrix.of_apply, ← mul_assoc, ← pow_add]
    exact (mul_div_cancel₀ _ (pow_ne_zero _ hh)).symm
  rw [he, Matrix.det_mul_column, show B.det = (∏ i : Fin p, h^i.val) * A.det from
    Matrix.det_mul_row _ _, pow_two]
  ring

#print axioms det_kernelGrid_eq_det_forwardDiff
#print axioms det_forwardDiff_eq_scaled

end Nuttall
