import W5.MathlibFiveSchurPivotDeterminant

/-!
# Match the exact five LDL checker pivots with shrinking Schur pivots

There are two already verified descriptions of Gaussian elimination:
* `realLDL5`: update the full 5×5 matrix, eliminating coordinates 0,1,2,3,4.
* `schurTail4`, `schurTail3`, `schurTail2`, `schurTail1`:
  successively take the trailing block of each exact Schur update.

For the diagonal pivot at each stage, these definitions agree exactly.
There is no determinant expansion or numerical hypothesis here.
The subsequent theorem may transport the signed pivots supplied by the
real interval checker to Mathlib's product formula.
-/

namespace W5

/-- Exact identification of the first pivot. -/
theorem realLDL5_pivot_zero_eq_schur
    (A : Matrix (Fin 5) (Fin 5) ℝ) :
    (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) = A 0 0 := by
  rfl

/-- Exact identification of the second pivot. -/
theorem realLDL5_pivot_one_eq_schur
    (A : Matrix (Fin 5) (Fin 5) ℝ) :
    (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) =
      (schurTail4 A) 0 0 := by
  rfl

/-- Exact identification of the third pivot. -/
theorem realLDL5_pivot_two_eq_schur
    (A : Matrix (Fin 5) (Fin 5) ℝ) :
    (realLDL5 A 2) (pivotIndexFive 2) (pivotIndexFive 2) =
      (schurTail3 A) 0 0 := by
  rfl

/-- Exact identification of the fourth pivot. -/
theorem realLDL5_pivot_three_eq_schur
    (A : Matrix (Fin 5) (Fin 5) ℝ) :
    (realLDL5 A 3) (pivotIndexFive 3) (pivotIndexFive 3) =
      (schurTail2 A) 0 0 := by
  rfl

/-- Exact identification of the fifth pivot. -/
theorem realLDL5_pivot_four_eq_schur
    (A : Matrix (Fin 5) (Fin 5) ℝ) :
    (realLDL5 A 4) (pivotIndexFive 4) (pivotIndexFive 4) =
      (schurTail1 A) 0 0 := by
  rfl

/-- The full genuine real-LDL determinant factorization, assembled
from the existing Mathlib determinant theorem and five pivot identities.
The hypotheses only require the first four actual pivots to be nonzero. -/
theorem det_five_eq_realLDL5_pivot_product
    (A : Matrix (Fin 5) (Fin 5) ℝ)
    (h0 : (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) ≠ 0)
    (h1 : (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) ≠ 0)
    (h2 : (realLDL5 A 2) (pivotIndexFive 2) (pivotIndexFive 2) ≠ 0)
    (h3 : (realLDL5 A 3) (pivotIndexFive 3) (pivotIndexFive 3) ≠ 0) :
    A.det =
      (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) *
      (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) *
      (realLDL5 A 2) (pivotIndexFive 2) (pivotIndexFive 2) *
      (realLDL5 A 3) (pivotIndexFive 3) (pivotIndexFive 3) *
      (realLDL5 A 4) (pivotIndexFive 4) (pivotIndexFive 4) := by
  have hp0 : A 0 0 ≠ 0 := by
    rwa [realLDL5_pivot_zero_eq_schur] at h0
  have hp1 : (schurTail4 A) 0 0 ≠ 0 := by
    rwa [realLDL5_pivot_one_eq_schur] at h1
  have hp2 : (schurTail3 A) 0 0 ≠ 0 := by
    rwa [realLDL5_pivot_two_eq_schur] at h2
  have hp3 : (schurTail2 A) 0 0 ≠ 0 := by
    rwa [realLDL5_pivot_three_eq_schur] at h3
  rw [det_five_eq_successive_schur_pivots A hp0 hp1 hp2 hp3]
  rw [realLDL5_pivot_zero_eq_schur,
    realLDL5_pivot_one_eq_schur, realLDL5_pivot_two_eq_schur,
    realLDL5_pivot_three_eq_schur, realLDL5_pivot_four_eq_schur]

end W5
