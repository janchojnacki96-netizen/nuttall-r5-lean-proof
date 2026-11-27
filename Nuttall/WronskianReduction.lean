import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block

namespace Nuttall

open Filter
open scoped BigOperators Topology

/-- The ordinary Wronskian of a family, using derivative orders as rows. -/
noncomputable def familyWronskian {p : ℕ} (f : Fin p → ℝ → ℝ) (x : ℝ) : ℝ :=
  (Matrix.of (fun (i j : Fin p) => iteratedDeriv i.val (f j) x)).det

/-- Multiplying every function by a common factor multiplies the Wronskian
by the corresponding power. The product rule is a lower triangular change of rows. -/
theorem familyWronskian_mul_left {n : ℕ} (a : ℝ → ℝ) (f : Fin (n+1) → ℝ → ℝ)
    (x : ℝ) (ha : ContDiffAt ℝ n a x)
    (hf : ∀ j, ContDiffAt ℝ n (f j) x) :
    familyWronskian (fun j t => a t * f j t) x =
      a x ^ (n+1) * familyWronskian f x := by
  let D (i j : ℕ) : ℝ :=
    if j ≤ i then (i.choose j : ℝ) * iteratedDeriv (i-j) a x else 0
  let T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of (fun i j => D i.val j.val)
  let F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    Matrix.of (fun i j => iteratedDeriv i.val (f j) x)
  have hT : T.IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := hij
    change D i.val j.val = 0
    simp only [D, if_neg (not_le_of_gt hij')]
  have hdet : T.det = a x ^ (n+1) := by
    rw [Matrix.det_of_isLowerTriangular T hT]
    simp [T, D]
  have hmat : (Matrix.of (fun (i j : Fin (n+1)) =>
      iteratedDeriv i.val (fun t => a t * f j t) x)) = T * F := by
    ext i j
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hcomm : (fun t => a t * f j t) = f j * a := funext (fun _ => mul_comm _ _)
    rw [Matrix.of_apply, hcomm, iteratedDeriv_mul ((hf j).of_le (by exact_mod_cast hi))
      (ha.of_le (by exact_mod_cast hi)), Matrix.mul_apply]
    change (∑ l ∈ Finset.range (i.val+1),
        (i.val.choose l : ℝ) * iteratedDeriv l (f j) x * iteratedDeriv (i.val-l) a x) =
      ∑ l : Fin (n+1), D i.val l.val * iteratedDeriv l.val (f j) x
    rw [Fin.sum_univ_eq_sum_range (fun l => D i.val l * iteratedDeriv l (f j) x)]
    rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hi))]
    · apply Finset.sum_congr rfl
      intro l hl
      have hli : l ≤ i.val := Nat.le_of_lt_succ (Finset.mem_range.1 hl)
      simp only [D, if_pos hli]
      ring
    · intro l _ hl
      have hnli : ¬l ≤ i.val := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hl
      simp only [D, if_neg hnli, zero_mul]
  unfold familyWronskian
  rw [hmat, Matrix.det_mul, hdet]

/-- The reduced family consists of the derivatives of the quotients by
the positive first function. Expanding the constant first column gives its Wronskian. -/
theorem familyWronskian_eq_pow_mul_reduced {n : ℕ} (f : Fin (n+1) → ℝ → ℝ)
    (x : ℝ) (hf : ∀ j, ContDiffAt ℝ n (f j) x) (h0 : f 0 x ≠ 0) :
    familyWronskian f x = f 0 x ^ (n+1) *
      familyWronskian (fun j => deriv (fun t => f j.succ t / f 0 t)) x := by
  let q : Fin (n+1) → ℝ → ℝ := Fin.cases (fun _ => 1)
    (fun j t => f j.succ t / f 0 t)
  have hq (j) : ContDiffAt ℝ n (q j) x := by
    refine Fin.cases ?_ (fun k => ?_) j
    · exact contDiffAt_const
    · exact (hf k.succ).div (hf 0) h0
  have hprod (j) : f j =ᶠ[𝓝 x] (fun t => f 0 t * q j t) := by
    refine Fin.cases ?_ (fun k => ?_) j
    · exact Eventually.of_forall (fun t => by simp [q])
    · filter_upwards [(hf 0).continuousAt.eventually_ne h0] with t ht
      change f k.succ t = f 0 t * (f k.succ t / f 0 t)
      field_simp
  have hW : familyWronskian f x =
      familyWronskian (fun j t => f 0 t * q j t) x := by
    unfold familyWronskian
    congr 1
    ext i j
    exact (hprod j).iteratedDeriv_eq i.val
  rw [hW, familyWronskian_mul_left _ _ _ (hf 0) hq]
  congr 1
  let Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    Matrix.of (fun i j => iteratedDeriv i.val (q j) x)
  have hfirst : Q 0 0 = 1 := by simp [Q, q]
  have hzero (i : Fin n) : Q i.succ 0 = 0 := by simp [Q, q, iteratedDeriv_succ']
  change Q.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hfirst, hzero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.succAbove_zero]
  unfold familyWronskian
  congr 1
  ext i j
  simp [Q, q, Matrix.submatrix, iteratedDeriv_succ']

#print axioms familyWronskian_mul_left
#print axioms familyWronskian_eq_pow_mul_reduced

end Nuttall
