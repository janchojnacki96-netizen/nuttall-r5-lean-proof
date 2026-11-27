import Nuttall.ShiftCore
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- The first (k) coefficients of (1/(1-X)), as a polynomial. -/
noncomputable def shiftGeometricPrefix {R : Type*} [Semiring R] (k : ℕ) : R[X] :=
  ∑ l ∈ Finset.range k, X^l

theorem shiftGeometricPrefix_mul_one_sub {R : Type*} [Ring R] (k : ℕ) :
    (shiftGeometricPrefix k : R[X]) * (1-X) = 1-X^k :=
  geom_sum_mul_neg _ _

/-- Multiplying by the geometric prefix takes cumulative sums up to order (k-1). -/
theorem coeff_shiftGeometricPrefix_mul {R : Type*} [Semiring R]
    (P : R[X]) {k i : ℕ} (hi : i < k) :
    ((shiftGeometricPrefix k : R[X]) * P).coeff i =
      ∑ l ∈ Finset.range (i+1), P.coeff (i-l) := by
  simp only [shiftGeometricPrefix, Finset.sum_mul, finsetSum_coeff, coeff_X_pow_mul']
  rw [← Finset.sum_subset (Finset.range_mono (by omega : i+1 ≤ k)) (fun l _ hl => by
    have hil : ¬ l ≤ i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
    simp [hil])]
  apply Finset.sum_congr rfl
  intro l hl
  simp [Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)]

/-- The matrix (U) that takes the same cumulative sums in the binomially normalized basis. -/
noncomputable def shiftTriangular (M k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i l => if l ≤ i then Real.sqrt ((M.choose l.val : ℝ) / M.choose i.val) else 0

/-- Read the first (k) rows and columns in the binomially normalized basis. -/
noncomputable def normalizedShiftCoefficients (M k : ℕ) (P : (ℝ[X])[X]) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => (P.coeff i.val).coeff j.val /
    Real.sqrt ((M.choose i.val : ℝ) * M.choose j.val)

private theorem sqrt_ratio_mul_normalized {a b c x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a/b) * (x / Real.sqrt (a*c)) = x / Real.sqrt (b*c) := by
  rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le, Real.sqrt_mul hb.le]
  field_simp [(Real.sqrt_pos.2 ha).ne', (Real.sqrt_pos.2 hb).ne', (Real.sqrt_pos.2 hc).ne']

private theorem sum_normalized_prefix {k : ℕ} (i : Fin k) (f : ℕ → ℝ) (a : ℝ) :
    (∑ l ∈ Finset.range (i.val+1), f (i.val-l)) / a =
      ∑ l : Fin k, if l.val ≤ i.val then f l.val / a else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun l => if l ≤ i.val then f l / a else 0)]
  have hsum := Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt i.isLt))
    (f := fun l => if l ≤ i.val then f l / a else 0)
    (fun l _ hl => by
      have hil : ¬ l ≤ i.val := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
      simp [hil])
  rw [← hsum, Finset.sum_div]
  calc
    _ = ∑ l ∈ Finset.range (i.val+1), f l / a := by
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun l => f l / a) (i.val+1))
    _ = _ := Finset.sum_congr rfl (fun l hl => by
      simp [Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)])

/-- The normalized matrix of multiplication by the outer geometric prefix. -/
theorem normalizedShiftCoefficients_geometric_left {M k : ℕ} (hk : k ≤ M+1)
    (P : (ℝ[X])[X]) :
    normalizedShiftCoefficients M k (shiftGeometricPrefix k * P) =
      shiftTriangular M k * normalizedShiftCoefficients M k P := by
  ext i j
  simp only [normalizedShiftCoefficients, shiftTriangular, Matrix.of_apply, Matrix.mul_apply,
    coeff_shiftGeometricPrefix_mul _ i.isLt, finsetSum_coeff]
  have hpos (l : Fin k) : 0 < (M.choose l.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (show l.val ≤ M by have := l.isLt; omega)
  simp_rw [ite_mul, zero_mul,
    sqrt_ratio_mul_normalized (hpos _) (hpos i) (hpos j)]
  exact sum_normalized_prefix i (fun l => (P.coeff l).coeff j.val) _

/-- The inner geometric prefix gives right multiplication by \(U^\top\). -/
theorem normalizedShiftCoefficients_geometric_right {M k : ℕ} (hk : k ≤ M+1)
    (P : (ℝ[X])[X]) :
    normalizedShiftCoefficients M k (C (shiftGeometricPrefix k) * P) =
      normalizedShiftCoefficients M k P * (shiftTriangular M k).transpose := by
  ext i j
  simp only [normalizedShiftCoefficients, shiftTriangular, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, coeff_C_mul, coeff_shiftGeometricPrefix_mul _ j.isLt]
  have hpos (l : Fin k) : 0 < (M.choose l.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (show l.val ≤ M by have := l.isLt; omega)
  have hnormalize (l : Fin k) :
      (P.coeff i.val).coeff l.val / Real.sqrt ((M.choose i.val : ℝ)*M.choose l.val) *
        Real.sqrt ((M.choose l.val : ℝ)/M.choose j.val) =
      (P.coeff i.val).coeff l.val / Real.sqrt ((M.choose i.val : ℝ)*M.choose j.val) := by
    rw [mul_comm, mul_comm (M.choose i.val : ℝ) (M.choose l.val),
      mul_comm (M.choose i.val : ℝ) (M.choose j.val)]
    exact sqrt_ratio_mul_normalized (hpos l) (hpos j) (hpos i)
  simp_rw [mul_ite, mul_zero, hnormalize]
  exact sum_normalized_prefix j (fun l => (P.coeff i.val).coeff l) _

#print axioms coeff_shiftGeometricPrefix_mul
#print axioms normalizedShiftCoefficients_geometric_left
#print axioms normalizedShiftCoefficients_geometric_right

end Nuttall
