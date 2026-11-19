import Mathlib

/-!
# Determinant congruences

The exact, assumption-free algebraic fact underlying the change of
coordinates in the W5 theta kernel.

Analytic differentiation and the identification of the particular
triangular Taylor matrix T are NOT proved here.
-/

namespace W5

theorem det_of_congruence (r : ℕ)
    (C T : Matrix (Fin r) (Fin r) ℝ) :
    (T * C * T.transpose).det = (T.det ^ 2) * C.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem det_of_congruence_pos_iff (r : ℕ)
    (C T : Matrix (Fin r) (Fin r) ℝ) (hT : T.det ≠ 0) :
    0 < (T * C * T.transpose).det ↔ 0 < C.det := by
  rw [det_of_congruence]
  have hsq : 0 < T.det ^ 2 := sq_pos_of_ne_zero hT
  constructor
  · intro hh
    by_contra hn
    have hc : C.det ≤ 0 := le_of_not_gt hn
    have hnonpos : (T.det ^ 2) * C.det ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hsq) hc
    linarith
  · intro hc
    exact mul_pos hsq hc

theorem det_of_congruence_neg_iff (r : ℕ)
    (C T : Matrix (Fin r) (Fin r) ℝ) (hT : T.det ≠ 0) :
    (T * C * T.transpose).det < 0 ↔ C.det < 0 := by
  rw [det_of_congruence]
  have hsq : 0 < T.det ^ 2 := sq_pos_of_ne_zero hT
  constructor
  · intro hh
    by_contra hn
    have hc : 0 ≤ C.det := le_of_not_gt hn
    have hnonneg : 0 ≤ (T.det ^ 2) * C.det :=
      mul_nonneg (le_of_lt hsq) hc
    linarith
  · intro hc
    exact mul_neg_of_pos_of_neg hsq hc

end W5
