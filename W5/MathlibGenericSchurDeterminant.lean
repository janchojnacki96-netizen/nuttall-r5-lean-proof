import W5.ThetaActualLeadingMinorOneTwoFromPivots
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Generic leading-pivot Schur determinant identity for ANY size

The first two actual theta leading-minor signs were obtained using
Mathlib's built-in determinant formulas for 1x1 and 2x2 matrices.
To cover orders THREE, FOUR and FIVE without manually expanding
determinants, reuse Mathlib's existing `Matrix.det_fromBlocks₁₁`.

For ANY real square matrix indexed by Fin (1+n) whose 0,0 entry
is nonzero, the first Schur pivot formula reads

  det(A) = A[0,0] * det(D - c*b/A[0,0]),

where D is the trailing n×n block and b,c are the original first
row/column. The result holds even if A is nonsymmetric.

The proof reindexes with the standard `finSumFinEquiv`, obtains a
unit invertible one-by-one corner from the nonzero pivot, and
invokes the existing Mathlib Schur determinant theorem. This single
lemma is designed for repeated use on the original 5×5 theta matrix.

This file only proves a universal matrix identity, and does not
assert any transcendental theta entry bounds or determinant signs.
-/

namespace W5

/-- The actual trailing real Schur complement after eliminating
the first row/column of an (n+1)x(n+1) matrix. -/
noncomputable def leadingSchurBlock (n : ℕ)
    (A : Matrix (Fin (1+n)) (Fin (1+n)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j =>
    A (Fin.natAdd 1 i) (Fin.natAdd 1 j) -
      A (Fin.natAdd 1 i) 0 * A 0 (Fin.natAdd 1 j) / A 0 0)

/-- This ONE general determinant formula replaces all manual
expansions for the 3x3, 4x4, and 5x5 leading theta matrices. -/
theorem det_eq_first_pivot_mul_leadingSchurBlock
    (n : ℕ) (A : Matrix (Fin (1+n)) (Fin (1+n)) ℝ)
    (hp : A 0 0 ≠ 0) :
    A.det = A 0 0 * (leadingSchurBlock n A).det := by
  classical
  let e : Fin 1 ⊕ Fin n ≃ Fin (1+n) := finSumFinEquiv
  let a : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.of (fun i j => A (e (Sum.inl i)) (e (Sum.inl j)))
  let b : Matrix (Fin 1) (Fin n) ℝ :=
    Matrix.of (fun i j => A (e (Sum.inl i)) (e (Sum.inr j)))
  let c : Matrix (Fin n) (Fin 1) ℝ :=
    Matrix.of (fun i j => A (e (Sum.inr i)) (e (Sum.inl j)))
  let d : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun i j => A (e (Sum.inr i)) (e (Sum.inr j)))
  have hzero : Fin.castAdd n (0 : Fin 1) = (0 : Fin (1+n)) := by
    apply Fin.ext
    rfl
  have ha : a 0 0 ≠ 0 := by
    simpa [a, e, hzero] using hp
  have hu : IsUnit a.det := by
    simpa [Matrix.det_fin_one] using
      (isUnit_iff_ne_zero.mpr ha)
  letI : Invertible a := a.invertibleOfIsUnitDet hu
  have hmul : (⅟a) 0 0 * a 0 0 = 1 := by
    have h := congrArg
      (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0)
      (invOf_mul_self a)
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using h
  have hinv : (⅟a) 0 0 = 1 / a 0 0 :=
    (eq_div_iff ha).2 hmul
  have hblocks : A.submatrix e e = Matrix.fromBlocks a b c d := by
    ext i j
    cases i <;> cases j <;> rfl
  have hschur :
      d - c * ⅟a * b = leadingSchurBlock n A := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.of_apply]
    simp only [Matrix.mul_apply, Fin.sum_univ_one]
    rw [hinv]
    simp [leadingSchurBlock, a, b, c, d, e, hzero, div_eq_mul_inv]
    ring
  have hdet :
      (A.submatrix e e).det = A.det :=
    Matrix.det_submatrix_equiv_self e A
  calc
    A.det = (A.submatrix e e).det := hdet.symm
    _ = (Matrix.fromBlocks a b c d).det := by rw [hblocks]
    _ = a.det * (d - c * ⅟a * b).det :=
      Matrix.det_fromBlocks₁₁ a b c d
    _ = A 0 0 * (leadingSchurBlock n A).det := by
      rw [Matrix.det_fin_one, hschur]
      rfl

end W5
