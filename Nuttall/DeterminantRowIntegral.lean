import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Ring

namespace Nuttall

open MeasureTheory
open scoped BigOperators

/-- Moving the first row to the end and negating the displaced rows
cancels the sign of the rotation. -/
theorem det_rotate_negated_rows (n : ℕ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    (Matrix.of fun (i j : Fin (n+1)) =>
      Fin.lastCases (motive := fun _ => ℝ) (A 0 j) (fun k : Fin n => -A k.succ j) i).det =
    A.det := by
  let c (i : Fin (n+1)) : ℝ := Fin.lastCases 1 (fun _ : Fin n => -1) i
  let B := A.submatrix (finRotate (n+1)) id
  have he : (Matrix.of fun (i j : Fin (n+1)) =>
      Fin.lastCases (motive := fun _ => ℝ) (A 0 j) (fun k : Fin n => -A k.succ j) i) =
      Matrix.of (fun i j => c i * B i j) := by
    ext i j
    refine Fin.lastCases ?_ (fun k : Fin n => ?_) i
    · simp [B, c]
    · simp [B, c]
  have hc : (∏ i, c i) = (-1:ℝ)^n := by
    rw [Fin.prod_univ_castSucc]
    simp [c]
  have hB : B.det = (-1:ℝ)^n * A.det := by
    change (A.submatrix (finRotate (n+1)) id).det = _
    rw [Matrix.det_permute, sign_finRotate]
    simp
  rw [he, Matrix.det_mul_column, hc, hB, ← mul_assoc, ← mul_pow]
  norm_num

private noncomputable def rowCofactor {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (i j : Fin (n+1)) : ℝ :=
  (-1:ℝ)^(i.val+j.val) * (A.submatrix i.succAbove j.succAbove).det

private theorem det_updateRow_eq_cofactors {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (i : Fin (n+1)) (row : Fin (n+1) → ℝ) :
    (A.updateRow i row).det = ∑ j, rowCofactor A i j * row j := by
  rw [Matrix.det_succ_row _ i]
  apply Finset.sum_congr rfl
  intro j _
  have hm : (A.updateRow i row).submatrix i.succAbove j.succAbove =
      A.submatrix i.succAbove j.succAbove := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.updateRow_ne (Fin.succAbove_ne i a)]
  rw [Matrix.updateRow_self, hm, rowCofactor]
  ring

theorem integrable_det_updateRow {n : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i : Fin (n+1))
    (g : Fin (n+1) → α → ℝ) (hg : ∀ j, Integrable (g j) μ) :
    Integrable (fun x => (A.updateRow i (fun j => g j x)).det) μ := by
  simp_rw [det_updateRow_eq_cofactors]
  exact integrable_finsetSum _ (fun j _ => (hg j).const_mul _)

/-- Integration commutes with the determinant when only one row varies. -/
theorem det_updateRow_integral {n : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i : Fin (n+1))
    (g : Fin (n+1) → α → ℝ) (hg : ∀ j, Integrable (g j) μ) :
    (A.updateRow i (fun j => ∫ x, g j x ∂μ)).det =
      ∫ x, (A.updateRow i (fun j => g j x)).det ∂μ := by
  simp_rw [det_updateRow_eq_cofactors]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · exact fun j _ => (hg j).const_mul _

theorem iteratedDeriv_det_updateRow {n d : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i : Fin (n+1))
    (g : Fin (n+1) → ℝ → ℝ) (hg : ∀ j, ContDiff ℝ d (g j)) (t : ℝ) :
    iteratedDeriv d (fun x => (A.updateRow i (fun j => g j x)).det) t =
      (A.updateRow i (fun j => iteratedDeriv d (g j) t)).det := by
  simp_rw [det_updateRow_eq_cofactors]
  rw [iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_const_mul_field]
  · intro j _
    exact (contDiff_const.mul (hg j)).contDiffAt

theorem contDiff_det_updateRow {n d : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (i : Fin (n+1)) (g : Fin (n+1) → ℝ → ℝ) (hg : ∀ j, ContDiff ℝ d (g j)) :
    ContDiff ℝ d (fun x => (A.updateRow i (fun j => g j x)).det) := by
  simp_rw [det_updateRow_eq_cofactors]
  exact ContDiff.sum (fun j _ => contDiff_const.mul (hg j))

/-- A nonnegative function on the open tail is positive somewhere if a
continuous derivative at its left endpoint is nonzero. -/
theorem exists_pos_on_right_of_iteratedDeriv_ne_zero {g : ℝ → ℝ} {d : ℕ} {t : ℝ}
    (hg : ContDiff ℝ d g) (hn : ∀ s > t, 0 ≤ g s)
    (hd : iteratedDeriv d g t ≠ 0) : ∃ s > t, 0 < g s := by
  by_contra! h
  have he : Set.EqOn g (fun _ => (0:ℝ)) (Set.Ioi t) :=
    fun s hs => le_antisymm (h s hs) (hn s hs)
  have hclosed : IsClosed {s | iteratedDeriv d g s = 0} :=
    isClosed_eq (hg.continuous_iteratedDeriv' d) continuous_const
  have hsubset : Set.Ioi t ⊆ {s | iteratedDeriv d g s = 0} := by
    intro s hs
    change iteratedDeriv d g s = 0
    rw [← iteratedDerivWithin_of_isOpen isOpen_Ioi hs, iteratedDerivWithin_congr he hs,
      iteratedDerivWithin_of_isOpen isOpen_Ioi hs]
    simp
  apply hd
  have ht : t ∈ closure (Set.Ioi t) := by
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr (le_refl t)
  exact closure_minimal hsubset hclosed ht

theorem integral_Ioi_pos_of_iteratedDeriv_ne_zero {g : ℝ → ℝ} {d : ℕ} {t : ℝ}
    (hg : ContDiff ℝ d g) (hI : IntegrableOn g (Set.Ioi t))
    (hn : ∀ s > t, 0 ≤ g s) (hd : iteratedDeriv d g t ≠ 0) :
    0 < ∫ s in Set.Ioi t, g s := by
  obtain ⟨s, hts, hpos⟩ := exists_pos_on_right_of_iteratedDeriv_ne_zero hg hn hd
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi t)] g :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun x hx => hn x hx)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hae hI).mpr
  let U := {s | 0 < g s} ∩ Set.Ioi t
  have hU : IsOpen U := (isOpen_lt continuous_const hg.continuous).inter isOpen_Ioi
  have hne : U.Nonempty := ⟨s, hpos, hts⟩
  have hsub : U ⊆ Function.support g ∩ Set.Ioi t := fun _ hx => ⟨hx.1.ne', hx.2⟩
  exact (hU.measure_pos volume hne).trans_le (measure_mono hsub)

#print axioms det_updateRow_integral
#print axioms iteratedDeriv_det_updateRow
#print axioms exists_pos_on_right_of_iteratedDeriv_ne_zero

end Nuttall
