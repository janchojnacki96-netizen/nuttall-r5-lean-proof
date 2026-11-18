import W5.PositiveTriangularCongruence

/-!
# The exact positive-factor determinant step in the theta coordinate change

The current kernel normalization contains a positive scalar c.
For a lower-triangular coordinate matrix T with positive diagonal,
every leading determinant of c • (T C Tᵀ) has exactly the sign of C.

This *algebraic* theorem is complete. The analytic identity asserting
that the normalized theta Taylor matrices have this form remains to
be proved separately.
-/

namespace W5

noncomputable def kernelNormalization (x : ℝ) : ℝ :=
  let y : ℝ := 1 / x ^ 2
  2 * Real.pi ^ ((1:ℝ) / 4) * Real.exp y / y ^ ((5:ℝ) / 4)

theorem kernelNormalization_pos (x : ℝ) (hx : 0 < x) :
    0 < kernelNormalization x := by
  have hy : (0:ℝ) < 1 / x ^ 2 :=
    div_pos (by norm_num) (sq_pos_of_pos hx)
  unfold kernelNormalization
  exact div_pos
    (mul_pos
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _))
      (Real.exp_pos _))
    (Real.rpow_pos_of_pos hy _)

theorem positiveScalarLowerTriangular_congruence_sign {r : ℕ}
    (C T : Matrix (Fin r) (Fin r) ℝ) (c : ℝ)
    (hc : 0 < c)
    (hlower : T.IsLowerTriangular)
    (hdiag : ∀ i : Fin r, 0 < T i i) :
    0 < (c • (T * C * T.transpose)).det ↔ 0 < C.det := by
  have hd : 0 < T.det := lowerTriangular_det_pos T hlower hdiag
  have hfactor : 0 < c ^ r * T.det ^ 2 :=
    mul_pos (pow_pos hc r) (sq_pos_of_pos hd)
  rw [Matrix.det_smul, det_of_congruence, Fintype.card_fin]
  rw [← mul_assoc]
  exact mul_pos_iff_of_pos_left hfactor

end W5
