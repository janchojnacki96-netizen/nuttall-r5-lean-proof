import W5.RealSchurTrailingDeterminantBridge

/-!
# Schur elimination commutes with restriction to a principal submatrix

This is a dimension-independent identity for the already verified
realSchurStep operator. The exact rational interval checker uses the same
real arithmetic update; a subsequent proof may restrict the sequence
to successively smaller trailing blocks.

Unlike expanding determinants, this requires no invertibility,
symmetry, or index-finiteness assumption. The proof is definitional,
because the original update is pointwise.

Together with the existing Mathlib-derived
`det_eq_first_pivot_mul_realSchurStep_tail`, this lemma removes
the repeated matrix-entry algebra from the 3x3 through 5x5 pivot
factorizations. It does NOT certify the numerical theta entries.
-/

namespace W5

/-- Restricting an exact Schur update to any principal submatrix
containing the pivot agrees with updating the restricted matrix. -/
theorem realSchurStep_submatrix
    {ι κ : Type*} (A : Matrix ι ι ℝ)
    (f : κ → ι) (k : κ) :
    (realSchurStep A (f k)).submatrix f f =
      realSchurStep (A.submatrix f f) k := by
  ext i j
  rfl

/-- Specialization for the successive trailing blocks of
matrices indexed by `Fin (n+1)`. -/
theorem realSchurStep_tail_commutes
    (n : ℕ)
    (A : Matrix (Fin (1+n)) (Fin (1+n)) ℝ)
    (k : Fin n) :
    (realSchurStep A (Fin.natAdd 1 k)).submatrix
      (Fin.natAdd 1) (Fin.natAdd 1) =
    realSchurStep
      (A.submatrix (Fin.natAdd 1) (Fin.natAdd 1)) k := by
  exact realSchurStep_submatrix A (Fin.natAdd 1) k

end W5
