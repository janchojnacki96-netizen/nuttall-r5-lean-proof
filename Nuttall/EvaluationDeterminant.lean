import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace Nuttall

open MeasureTheory Set
open scoped BigOperators

/-- Subtracting consecutive rows of the normalized evaluation matrix leaves
one minor of differences, with the original first column as a prefactor. -/
theorem det_eval_eq_prod_mul_det_differences {n : ℕ}
    (f : Fin (n+1) → ℝ → ℝ) (u : Fin (n+1) → ℝ)
    (h : ∀ i, f 0 (u i) ≠ 0) :
    (Matrix.of (fun i j => f j (u i))).det =
      (∏ i, f 0 (u i)) *
        (Matrix.of (fun (i j : Fin n) =>
          f j.succ (u i.succ) / f 0 (u i.succ) -
          f j.succ (u i.castSucc) / f 0 (u i.castSucc))).det := by
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    Matrix.of (fun i j => f j (u i) / f 0 (u i))
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    Matrix.of (fun i => Fin.cases (A 0) (fun k j => A k.succ j - A k.castSucc j) i)
  have hAB : A.det = B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
    · intro j
      simp [B]
    · intro i j
      simp [B]
  have hfirst (i) : A i 0 = 1 := div_self (h i)
  have hdetB : B.det =
      (Matrix.of (fun (i j : Fin n) =>
        A i.succ j.succ - A i.castSucc j.succ)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hz (i : Fin n) : B i.succ 0 = 0 := by simp [B, hfirst]
    simp [hz, B, hfirst, Matrix.submatrix]
  have hscaled : (Matrix.of (fun i j => f j (u i))) =
      (Matrix.of (fun i j => f 0 (u i) * A i j)) := by
    ext i j
    simp [A, h i, mul_comm (f 0 (u i))]
  rw [hscaled]
  change (Matrix.of (fun i j => f 0 (u i) * A i j)).det = _
  rw [Matrix.det_mul_column, hAB, hdetB]
  rfl

private theorem det_eq_perm_prod_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) *
      ∏ i, A i (σ i) := by
  rw [← Matrix.det_transpose A, Matrix.det_apply']
  rfl

/-- A determinant of rowwise integrals is the integral of the determinant
over the product of the row measures. -/
theorem det_integral_rows {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (g : Fin n → ℝ → ℝ)
    (hg : ∀ i j, Integrable (g j) (μ i)) :
    (Matrix.of (fun i j => ∫ x, g j x ∂μ i)).det =
      ∫ x : Fin n → ℝ, (Matrix.of (fun i j => g j (x i))).det ∂Measure.pi μ := by
  classical
  simp only [det_eq_perm_prod_rows, Matrix.of_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [integral_const_mul, integral_fintype_prod_eq_prod (μ := μ) (fun i x => g (σ i) x)]
  · intro σ _
    exact (Integrable.fintype_prod (μ := μ) (fun i => hg i (σ i))).const_mul _

/-- The entries in each row depend only on that row's integration variable. -/
theorem integrable_evaluation_det {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (g : Fin n → ℝ → ℝ)
    (hg : ∀ i j, Integrable (g j) (μ i)) :
    Integrable (fun x : Fin n → ℝ => (Matrix.of (fun i j => g j (x i))).det)
      (Measure.pi μ) := by
  classical
  simp only [det_eq_perm_prod_rows, Matrix.of_apply]
  exact integrable_finsetSum _ (fun σ _ =>
    (Integrable.fintype_prod (μ := μ) (fun i => hg i (σ i))).const_mul _)

/-- One step of the evaluation determinant reduction in §4.1. The derivative
and regularity argument supplies the interval identities `hFTC`. -/
theorem det_eval_eq_prod_mul_integral {n : ℕ} (f : Fin (n+1) → ℝ → ℝ)
    (u : Fin (n+1) → ℝ) (g : Fin n → ℝ → ℝ)
    (hu : Monotone u) (h : ∀ i, f 0 (u i) ≠ 0)
    (hg : ∀ (i j : Fin n), IntervalIntegrable (g j) volume (u i.castSucc) (u i.succ))
    (hFTC : ∀ (i j : Fin n), (∫ x in u i.castSucc..u i.succ, g j x) =
      f j.succ (u i.succ) / f 0 (u i.succ) -
        f j.succ (u i.castSucc) / f 0 (u i.castSucc)) :
    (Matrix.of (fun i j => f j (u i))).det =
      (∏ i, f 0 (u i)) * ∫ x : Fin n → ℝ, (Matrix.of (fun i j => g j (x i))).det
        ∂Measure.pi (fun i => volume.restrict (Ioc (u i.castSucc) (u i.succ))) := by
  have hle (i : Fin n) : u i.castSucc ≤ u i.succ := hu (by simp [Fin.le_def])
  rw [det_eval_eq_prod_mul_det_differences f u h]
  congr 1
  simp_rw [← hFTC, intervalIntegral.integral_of_le (hle _)]
  exact det_integral_rows _ g (fun i j => (hg i j).1)

/-- Strictly increasing original nodes produce disjoint ordered open-on-the-left
intervals. This remains true when an integration variable is a right endpoint. -/
theorem strictMono_of_adjacent_Ioc {n : ℕ} {u : Fin (n+1) → ℝ}
    (hu : Monotone u) {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ Ioc (u i.castSucc) (u i.succ)) : StrictMono x := by
  intro i j hij
  have hij' : i.succ ≤ j.castSucc := by
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    exact Nat.succ_le_of_lt hij
  exact (hx i).2.trans_lt ((hu hij').trans_lt (hx j).1)

/-- Countably many excluded points in each interval do not affect strict
positivity of an integrable function on the product of adjacent intervals. -/
theorem integral_adjacent_Ioc_pos {n : ℕ} {u : Fin (n+1) → ℝ}
    (hu : StrictMono u) {S : Set ℝ} (hS : S.Countable)
    (F : (Fin n → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi (fun i =>
      volume.restrict (Ioc (u i.castSucc) (u i.succ)))))
    (hpos : ∀ x, (∀ i, x i ∈ Ioc (u i.castSucc) (u i.succ) ∧ x i ∉ S) → 0 < F x) :
    0 < ∫ x, F x ∂Measure.pi (fun i => volume.restrict (Ioc (u i.castSucc) (u i.succ))) := by
  let μ (i : Fin n) := volume.restrict (Ioc (u i.castSucc) (u i.succ))
  have hcoords : ∀ᵐ x ∂Measure.pi μ, ∀ i, x i ∈ Ioc (u i.castSucc) (u i.succ) ∧ x i ∉ S := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := μ) (i := i)).eventually
      ((ae_restrict_mem measurableSet_Ioc).and (hS.ae_notMem (μ i)))
  have hpos' : ∀ᵐ x ∂Measure.pi μ, 0 < F x := hcoords.mono hpos
  have hμ : Measure.pi μ ≠ 0 := by
    intro hz
    have hmass : 0 < Measure.pi μ univ := by
      rw [Measure.pi_univ]
      apply pos_iff_ne_zero.2
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      have hi : i.castSucc < i.succ := by simp [Fin.lt_def]
      simpa [μ, Measure.restrict_apply, Real.volume_Ioc] using hu hi
    simp [hz] at hmass
  have : (ae (Measure.pi μ)).NeBot := ae_neBot.2 hμ
  apply lt_of_le_of_ne (integral_nonneg_of_ae (hpos'.mono fun _ hx => hx.le))
  intro hz
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (hpos'.mono fun _ hx => hx.le) hF).1 hz.symm
  exact (hpos'.and hzero).exists.elim fun _ hx => hx.1.ne' hx.2

/-- The fundamental theorem for an absolutely continuous quotient recovers
exactly the row difference used by the determinant reduction. -/
theorem det_eval_eq_prod_mul_integral_deriv {n : ℕ} (f : Fin (n+1) → ℝ → ℝ)
    (u : Fin (n+1) → ℝ) (hu : Monotone u)
    (h : ∀ i, f 0 (u i) ≠ 0)
    (hac : ∀ (i j : Fin n), AbsolutelyContinuousOnInterval
      (fun x => f j.succ x / f 0 x) (u i.castSucc) (u i.succ)) :
    (Matrix.of (fun i j => f j (u i))).det =
      (∏ i, f 0 (u i)) * ∫ x : Fin n → ℝ,
        (Matrix.of (fun i j => deriv (fun t => f j.succ t / f 0 t) (x i))).det
        ∂Measure.pi (fun i => volume.restrict (Ioc (u i.castSucc) (u i.succ))) :=
  det_eval_eq_prod_mul_integral f u _ hu h
    (fun i j => (hac i j).intervalIntegrable_deriv)
    (fun i j => (hac i j).integral_deriv_eq_sub)

/-- Positivity transfers back from the reduced family evaluated at nodes
in the consecutive integration intervals, outside a countable exceptional set. -/
theorem det_eval_pos_of_reduced {n : ℕ} (f : Fin (n+1) → ℝ → ℝ)
    (u : Fin (n+1) → ℝ) (hu : StrictMono u)
    (h : ∀ i, 0 < f 0 (u i)) {S : Set ℝ} (hS : S.Countable)
    (hac : ∀ (i j : Fin n), AbsolutelyContinuousOnInterval
      (fun x => f j.succ x / f 0 x) (u i.castSucc) (u i.succ))
    (hred : ∀ x : Fin n → ℝ, StrictMono x →
      (∀ i, x i ∈ Ioc (u i.castSucc) (u i.succ)) → (∀ i, x i ∉ S) →
      0 < (Matrix.of (fun i j => deriv (fun t => f j.succ t / f 0 t) (x i))).det) :
    0 < (Matrix.of (fun i j => f j (u i))).det := by
  rw [det_eval_eq_prod_mul_integral_deriv f u hu.monotone (fun i => (h i).ne') hac]
  apply mul_pos (Finset.prod_pos (fun i _ => h i))
  apply integral_adjacent_Ioc_pos hu hS
  · exact integrable_evaluation_det _ _ (fun i j => (hac i j).intervalIntegrable_deriv.1)
  · intro x hx
    exact hred x (strictMono_of_adjacent_Ioc hu.monotone (fun i => (hx i).1))
      (fun i => (hx i).1) (fun i => (hx i).2)

#print axioms det_eval_eq_prod_mul_det_differences
#print axioms integral_adjacent_Ioc_pos
#print axioms det_eval_eq_prod_mul_integral_deriv
#print axioms det_eval_pos_of_reduced

end Nuttall
