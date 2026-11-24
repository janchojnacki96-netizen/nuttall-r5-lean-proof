import W5.MathlibGenericSchurDeterminant
import W5.VerifiedIntervalRealLDL5

/-!
# Exact bridge between Mathlib Schur determinants and the real LDL checker

The existing real interval checker propagates the pointwise update
`realSchurStep`. The universal determinant identity established in
`W5.MathlibGenericSchurDeterminant` uses the trailing block
`leadingSchurBlock`.

Those objects agree definitionally: both update the (i,j) entry by
Aᵢⱼ - Aᵢ₀ A₀ⱼ / A₀₀ on the trailing indices.
Here we prove that identification once for every size, and reuse the
previous Mathlib determinant lemma to obtain the exact first elimination
step for ANY real matrix, without determinant expansions.

This does not assume or assert any sign of a theta determinant or any
numerical enclosure. Iterating this result and matching all five
checker pivots with leading principal minors remain separate tasks.
-/

namespace W5

/-- The true trailing part of one full real LDL update is exactly
the Schur complement used in the Mathlib block determinant identity. -/
theorem leadingSchurBlock_eq_realSchurStep_tail
    (n : ℕ) (A : Matrix (Fin (1+n)) (Fin (1+n)) ℝ) :
    leadingSchurBlock n A =
      (realSchurStep A 0).submatrix (Fin.natAdd 1) (Fin.natAdd 1) := by
  ext i j
  rfl

/-- First determinant reduction using the EXACT update already used
by the verified real interval algorithm. The only hypothesis is that
the pivot is nonzero; no matrix-sign premise is assumed. -/
theorem det_eq_first_pivot_mul_realSchurStep_tail
    (n : ℕ) (A : Matrix (Fin (1+n)) (Fin (1+n)) ℝ)
    (hp : A 0 0 ≠ 0) :
    A.det = A 0 0 *
      ((realSchurStep A 0).submatrix
        (Fin.natAdd 1) (Fin.natAdd 1)).det := by
  rw [det_eq_first_pivot_mul_leadingSchurBlock n A hp,
    leadingSchurBlock_eq_realSchurStep_tail n A]

end W5
