import W5.DeterminantCongruence
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Strict sign preservation under triangular coordinate changes

This lemma completes the abstract matrix-algebra portion of the
Nuttall r=5 bridge: every lower-triangular coordinate matrix with
strictly positive diagonal has positive determinant, and therefore
its two-sided congruence preserves both determinant signs.

It does NOT yet identify the particular theta Taylor-jet coordinate
transformation with the lower-triangular matrix here.
-/

namespace W5

theorem lowerTriangular_det_pos {r : ℕ}
    (T : Matrix (Fin r) (Fin r) ℝ)
    (hlower : T.IsLowerTriangular)
    (hdiag : ∀ i : Fin r, 0 < T i i) :
    0 < T.det := by
  rw [Matrix.det_of_isLowerTriangular T hlower]
  exact Finset.prod_pos fun i _ => hdiag i

theorem lowerTriangular_congruence_preserves_positive {r : ℕ}
    (C T : Matrix (Fin r) (Fin r) ℝ)
    (hlower : T.IsLowerTriangular)
    (hdiag : ∀ i : Fin r, 0 < T i i) :
    0 < (T * C * T.transpose).det ↔ 0 < C.det := by
  have hdet : T.det ≠ 0 :=
    ne_of_gt (lowerTriangular_det_pos T hlower hdiag)
  exact det_of_congruence_pos_iff r C T hdet

theorem lowerTriangular_congruence_preserves_negative {r : ℕ}
    (C T : Matrix (Fin r) (Fin r) ℝ)
    (hlower : T.IsLowerTriangular)
    (hdiag : ∀ i : Fin r, 0 < T i i) :
    (T * C * T.transpose).det < 0 ↔ C.det < 0 := by
  have hdet : T.det ≠ 0 :=
    ne_of_gt (lowerTriangular_det_pos T hlower hdiag)
  exact det_of_congruence_neg_iff r C T hdet

end W5
