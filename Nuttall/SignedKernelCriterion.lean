import Nuttall.CentralEvaluationPositivity
import Nuttall.Existence

namespace Nuttall

open Set
open scoped BigOperators ContDiff

def kernelMinorSign (p : ℕ) : ℝ := (-1 : ℝ) ^ (p * (p - 1) / 2)

private theorem det_alternating_columns {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    (Matrix.of (fun i j : Fin p => (-1:ℝ)^j.val * A i j)).det = kernelMinorSign p * A.det := by
  rw [Matrix.det_mul_row, kernelMinorSign, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

private theorem iteratedDeriv_iterated_real (f : ℝ → ℝ) (a b : ℕ) :
    iteratedDeriv a (iteratedDeriv b f) = iteratedDeriv (a+b) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

private theorem contDiff_iterated_real {f : ℝ → ℝ} {N : ℕ} (hf : ContDiff ℝ N f)
    {a b : ℕ} (h : a+b ≤ N) : ContDiff ℝ a (iteratedDeriv b f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv' a b (hf.of_le (by exact_mod_cast h))

private theorem det_eval_pos_of_contDiff_family {n : ℕ} (f : Fin (n+1) → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ n (f i))
    (hW : ∀ k (hk : k ≤ n) x, 0 < x →
      0 < familyWronskian (fun j : Fin (k+1) => f (j.castLE (Nat.succ_le_succ hk))) x)
    (u : Fin (n+1) → ℝ) (hu : StrictMono u) (hu₀ : ∀ i, 0 < u i) :
    0 < (Matrix.of (fun i j => f j (u i))).det := by
  let B := u (Fin.last n) + 1
  have huB (i : Fin (n+1)) : u i ∈ Ioo (0:ℝ) B := by
    refine ⟨hu₀ i, ?_⟩
    have h := hu.monotone (Fin.le_last i)
    dsimp [B]
    linarith
  refine det_eval_pos_of_familyWronskians (S := ∅) countable_empty f ?_ ?_ ?_ ?_ u hu huB (by simp)
  · intro j m hm
    exact ((hf j).of_le (by exact_mod_cast (show m ≤ n by omega))).contDiffOn
  · intro j m hm
    exact (contDiff_iterated_real (hf j) (a := 1) (b := m) (by omega)).contDiffOn.locallyLipschitzOn
      (convex_Ioo _ _)
  · intro j x _ _
    exact (hf j).contDiffAt
  · intro k hk x hx _
    exact hW k hk x hx.1

/-- First application of the evaluation criterion, to consecutive derivatives
translated by a fixed positive node. -/
theorem signed_derivative_evaluation_pos {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(2*n) : ℕ∞ω) f)
    (hW : ∀ p : ℕ, 1 ≤ p → p ≤ n+1 → ∀ t : ℝ, 0 < t →
      0 < kernelMinorSign p * wronskian f p t)
    (x : ℝ) (hx : 0 < x) (y : Fin (n+1) → ℝ) (hy : StrictMono y) (hy₀ : ∀ j, 0 < y j) :
    0 < kernelMinorSign (n+1) *
      (Matrix.of (fun (i j : Fin (n+1)) => iteratedDeriv j.val f (x+y i))).det := by
  let g (j : Fin (n+1)) (t : ℝ) := (-1:ℝ)^j.val * iteratedDeriv j.val f (x+t)
  have hg (j : Fin (n+1)) : ContDiff ℝ n (g j) := by
    have hj := j.isLt
    exact contDiff_const.mul ((contDiff_iterated_real hf (a := n) (b := j.val)
      (by omega)).comp (by fun_prop))
  have hjet (i : ℕ) (j : Fin (n+1)) (t : ℝ) :
      iteratedDeriv i (g j) t = (-1:ℝ)^j.val * iteratedDeriv (i+j.val) f (x+t) := by
    dsimp [g]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_add, iteratedDeriv_iterated_real]
  have hprefix (k : ℕ) (hk : k ≤ n) (t : ℝ) (ht : 0 < t) :
      0 < familyWronskian (fun j : Fin (k+1) => g (j.castLE (Nat.succ_le_succ hk))) t := by
    have hmat : (Matrix.of (fun (i j : Fin (k+1)) =>
        iteratedDeriv i.val (g (j.castLE (Nat.succ_le_succ hk))) t)) =
        Matrix.of (fun (i j : Fin (k+1)) => (-1:ℝ)^j.val * iteratedDeriv (i.val+j.val) f (x+t)) := by
      ext i j
      exact hjet i.val _ t
    let M := Matrix.of (fun (i j : Fin (k+1)) => iteratedDeriv (i.val+j.val) f (x+t))
    have h := hW (k+1) (by omega) (by omega) (x+t) (by linarith)
    change 0 < kernelMinorSign (k+1) * M.det at h
    rw [← det_alternating_columns M] at h
    rw [familyWronskian, hmat]
    exact h
  have h := det_eval_pos_of_contDiff_family g hg hprefix y hy hy₀
  rw [← det_alternating_columns
    (Matrix.of (fun (i j : Fin (n+1)) => iteratedDeriv j.val f (x+y i)))]
  exact h

/-- A signed Hankel Wronskian test implies strict reverse sign regularity
for the addition kernel. The second evaluation uses translates of the
original function and the first evaluation supplies their Wronskians. -/
theorem signed_kernel_evaluation_pos {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(2*n) : ℕ∞ω) f)
    (hW : ∀ p : ℕ, 1 ≤ p → p ≤ n+1 → ∀ t : ℝ, 0 < t →
      0 < kernelMinorSign p * wronskian f p t)
    (x y : Fin (n+1) → ℝ) (hx : StrictMono x) (hy : StrictMono y)
    (hx₀ : ∀ i, 0 < x i) (hy₀ : ∀ j, 0 < y j) :
    0 < kernelMinorSign (n+1) * (Matrix.of (fun (i j : Fin (n+1)) => f (x i+y j))).det := by
  let g (j : Fin (n+1)) (t : ℝ) := (-1:ℝ)^j.val * f (t+y j)
  have hg (j : Fin (n+1)) : ContDiff ℝ n (g j) :=
    contDiff_const.mul ((hf.of_le (by exact_mod_cast (show n ≤ 2*n by omega))).comp (by fun_prop))
  have hjet (i : ℕ) (j : Fin (n+1)) (t : ℝ) :
      iteratedDeriv i (g j) t = (-1:ℝ)^j.val * iteratedDeriv i f (t+y j) := by
    dsimp [g]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]
  have hprefix (k : ℕ) (hk : k ≤ n) (t : ℝ) (ht : 0 < t) :
      0 < familyWronskian (fun j : Fin (k+1) => g (j.castLE (Nat.succ_le_succ hk))) t := by
    let y' (j : Fin (k+1)) := y (j.castLE (Nat.succ_le_succ hk))
    have hy' : StrictMono y' := fun i j hij => hy hij
    have h := signed_derivative_evaluation_pos (n := k)
      (hf.of_le (by exact_mod_cast (show 2*k ≤ 2*n by omega)))
      (fun p hp hp' => hW p hp (by omega)) t ht y' hy' (fun j => hy₀ _)
    have hmat : (Matrix.of (fun (i j : Fin (k+1)) =>
        iteratedDeriv i.val (g (j.castLE (Nat.succ_le_succ hk))) t)) =
        Matrix.of (fun (i j : Fin (k+1)) => (-1:ℝ)^j.val *
          (Matrix.of (fun (a b : Fin (k+1)) => iteratedDeriv b.val f (t+y' a))).transpose i j) := by
      ext i j
      exact hjet i.val _ t
    let M := Matrix.of (fun (a b : Fin (k+1)) => iteratedDeriv b.val f (t+y' a))
    change 0 < kernelMinorSign (k+1) * M.det at h
    rw [← Matrix.det_transpose M, ← det_alternating_columns M.transpose] at h
    rw [familyWronskian, hmat]
    exact h
  have h := det_eval_pos_of_contDiff_family g hg hprefix x hx hx₀
  rw [← det_alternating_columns (Matrix.of (fun (i j : Fin (n+1)) => f (x i+y j)))]
  exact h

#print axioms signed_derivative_evaluation_pos
#print axioms signed_kernel_evaluation_pos

end Nuttall
