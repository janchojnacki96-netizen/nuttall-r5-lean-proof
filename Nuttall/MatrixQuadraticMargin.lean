import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Nuttall

open scoped Matrix

private theorem dotProduct_self_pos_of_ne_zero {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  have hpos : 0 < x i * x i := by simpa only [pow_two] using sq_pos_of_ne_zero hi
  unfold dotProduct
  exact hpos.trans_le (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))

/-- A matrix with a strictly positive real quadratic form has positive
determinant. Symmetry is unnecessary for this determinant sign. -/
theorem det_pos_of_quadratic_margin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (h : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) :
    0 < A.det := by
  let path (t : ℝ) := (1-t) • (1 : Matrix ι ι ℝ) + t • A
  let f (t : ℝ) := (path t).det
  have hf : Continuous f := by apply Continuous.matrix_det; fun_prop
  have hzero : f 0 = 1 := by simp [f, path]
  have hone : f 1 = A.det := by simp [f, path]
  have hno (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : f t ≠ 0 := by
    intro hdet
    obtain ⟨x, hx, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hform :
        x ⬝ᵥ (path t *ᵥ x) = (1-t)*(x ⬝ᵥ x) + t*(x ⬝ᵥ (A *ᵥ x)) := by
      simp [path, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
    have hform_pos : 0 < x ⬝ᵥ (path t *ᵥ x) := by
      rw [hform]
      by_cases htz : t = 0
      · simpa [htz] using dotProduct_self_pos_of_ne_zero hx
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr ht.2) (dotProduct_self_pos_of_ne_zero hx).le)
          (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm htz)) (h x hx))
    rw [hkernel, dotProduct_zero] at hform_pos
    exact (lt_irrefl 0) hform_pos
  by_contra! hn
  have hm : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := by simp [hzero, hone, hn]
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num) hf.continuousOn hm
  exact hno t ht he

private theorem quadratic_lower_of_entry_bounds {ι : Type*} [Fintype ι] (E : Matrix ι ι ℝ)
    (x : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hE : ∀ i j, |E i j| ≤ ε) :
    -(ε*(Fintype.card ι:ℝ)^2)*(x ⬝ᵥ x) ≤ x ⬝ᵥ (E *ᵥ x) := by
  classical
  have hsq (i : ι) : (x i)^2 ≤ x ⬝ᵥ x := by
    unfold dotProduct
    rw [pow_two]
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  have hprod (i j : ι) : |x i| * |x j| ≤ x ⬝ᵥ x := by
    have h := two_mul_le_add_sq (|x i|) (|x j|)
    rw [sq_abs, sq_abs] at h
    nlinarith only [h, hsq i, hsq j]
  have hterm (i j : ι) : -(ε*(x ⬝ᵥ x)) ≤ x i * (E i j * x j) := by
    apply (abs_le.mp ?_).1
    simp only [abs_mul]
    rw [show |x i| * (|E i j| * |x j|) = |E i j| * (|x i| * |x j|) by ring]
    exact mul_le_mul (hE i j) (hprod i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hε
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm i j)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have he : x ⬝ᵥ (E *ᵥ x) = ∑ i, ∑ j, x i*(E i j*x j) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [he]
  convert hsum using 1
  ring

/-- A positive quadratic margin persists under an entrywise small perturbation. -/
theorem det_pos_of_quadratic_entry_margin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A E : Matrix ι ι ℝ) {μ ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ x : ι → ℝ, μ*(x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (hE : ∀ i j, |E i j| ≤ ε) (hμ : ε*(Fintype.card ι:ℝ)^2 < μ) :
    0 < (A+E).det := by
  apply det_pos_of_quadratic_margin
  intro x hx
  rw [Matrix.add_mulVec, dotProduct_add]
  have hpos := mul_pos (sub_pos.mpr hμ) (dotProduct_self_pos_of_ne_zero hx)
  linarith only [hpos, hA x, quadratic_lower_of_entry_bounds E x hε hE]

#print axioms det_pos_of_quadratic_margin
#print axioms det_pos_of_quadratic_entry_margin

end Nuttall
