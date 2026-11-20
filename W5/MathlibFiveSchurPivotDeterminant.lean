import W5.RealSchurSubmatrix

/-!
# Actual five-by-five determinant as a product of exact Schur pivots

Mathlib already proves the general block identity
`Matrix.det_fromBlocks₁₁`. The project's generic theorem
`det_eq_first_pivot_mul_leadingSchurBlock` derives one pivot
factorization from it. This module iterates that SAME theorem
four times for an arbitrary 5x5 real matrix.

Every auxiliary matrix is the actual trailing Schur complement;
there is NO determinant expansion, no symmetry assumption, and
no theta sign or numerical premise. The first four nonzero-pivot
hypotheses are needed for the Schur complement formula, and are
kept explicit.

The distinct next obligation is to identify these shrinking-block
pivots with the five `realLDL5` pivots already signed by the
verified interval algorithm.
-/

namespace W5

noncomputable def schurTail4
    (A : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  leadingSchurBlock 4 A

noncomputable def schurTail3
    (A : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  leadingSchurBlock 3 (schurTail4 A)

noncomputable def schurTail2
    (A : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  leadingSchurBlock 2 (schurTail3 A)

noncomputable def schurTail1
    (A : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  leadingSchurBlock 1 (schurTail2 A)

/-- Full 5x5 determinant factorization into true successive
Schur pivots. Only the first four must be nonzero. -/
theorem det_five_eq_successive_schur_pivots
    (A : Matrix (Fin 5) (Fin 5) ℝ)
    (h0 : A 0 0 ≠ 0)
    (h1 : (schurTail4 A) 0 0 ≠ 0)
    (h2 : (schurTail3 A) 0 0 ≠ 0)
    (h3 : (schurTail2 A) 0 0 ≠ 0) :
    A.det =
      A 0 0 * (schurTail4 A) 0 0 *
      (schurTail3 A) 0 0 * (schurTail2 A) 0 0 *
      (schurTail1 A) 0 0 := by
  have hA :
      A.det = A 0 0 * (schurTail4 A).det :=
    det_eq_first_pivot_mul_leadingSchurBlock 4 A h0
  have hB :
      (schurTail4 A).det =
        (schurTail4 A) 0 0 * (schurTail3 A).det :=
    det_eq_first_pivot_mul_leadingSchurBlock 3 (schurTail4 A) h1
  have hC :
      (schurTail3 A).det =
        (schurTail3 A) 0 0 * (schurTail2 A).det :=
    det_eq_first_pivot_mul_leadingSchurBlock 2 (schurTail3 A) h2
  have hD :
      (schurTail2 A).det =
        (schurTail2 A) 0 0 * (schurTail1 A).det :=
    det_eq_first_pivot_mul_leadingSchurBlock 1 (schurTail2 A) h3
  have hE : (schurTail1 A).det = (schurTail1 A) 0 0 := by
    rw [Matrix.det_fin_one]
  calc
    A.det = A 0 0 * (schurTail4 A).det := hA
    _ = A 0 0 * (schurTail4 A) 0 0 *
          (schurTail3 A).det := by rw [hB]; ring
    _ = A 0 0 * (schurTail4 A) 0 0 *
          (schurTail3 A) 0 0 * (schurTail2 A).det := by rw [hC]; ring
    _ = A 0 0 * (schurTail4 A) 0 0 *
          (schurTail3 A) 0 0 * (schurTail2 A) 0 0 *
          (schurTail1 A).det := by rw [hD]; ring
    _ = A 0 0 * (schurTail4 A) 0 0 *
          (schurTail3 A) 0 0 * (schurTail2 A) 0 0 *
          (schurTail1 A) 0 0 := by rw [hE]

end W5
