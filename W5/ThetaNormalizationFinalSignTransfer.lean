import W5.ThetaNormalizationMatrixCongruence
import W5.OriginalJetSignBridge
import W5.Range

namespace W5

/-- Both determinant signs are preserved by the actual kernel
normalization: the scalar and the squared triangular determinant
are strictly positive. -/
theorem analyticLeadingMatrix_det_factor
    (r : ℕ) (hr : r ≤ 5) (t : ℝ) (ht : 0 ≤ t) :
    (analyticLeadingMatrix r hr (xOfT t)).det =
      (kernelNormalization (xOfT t)^r *
        (thetaNormTriangular r (xOfT t)).det^2) * W r t := by
  rw [analyticLeadingMatrix_eq_normalization_congruence,
    Matrix.det_smul, det_of_congruence, Fintype.card_fin,
    thetaTimeOfX_xOfT, W_eq_originalPsiJet_det r hr t]
  ring

theorem analyticLeadingMatrix_det_factor_pos
    (r : ℕ) (hr : r ≤ 5) (t : ℝ) (ht : 0 ≤ t) :
    0 < kernelNormalization (xOfT t)^r *
      (thetaNormTriangular r (xOfT t)).det^2 := by
  have hx := (xOfT_positive_and_bounded t ht).1
  have hd := lowerTriangular_det_pos (thetaNormTriangular r (xOfT t))
    (thetaNormTriangular_lower r hr (xOfT t))
    (thetaNormTriangular_diag_pos r hr (xOfT t) hx)
  exact mul_pos (pow_pos (kernelNormalization_pos _ hx) r) (sq_pos_of_pos hd)

theorem analyticLeadingMatrix_positive_iff_W
    (r : ℕ) (hr : r ≤ 5) (t : ℝ) (ht : 0 ≤ t) :
    0 < (analyticLeadingMatrix r hr (xOfT t)).det ↔ 0 < W r t := by
  rw [analyticLeadingMatrix_det_factor r hr t ht]
  exact mul_pos_iff_of_pos_left (analyticLeadingMatrix_det_factor_pos r hr t ht)

theorem analyticLeadingMatrix_negative_iff_W
    (r : ℕ) (hr : r ≤ 5) (t : ℝ) (ht : 0 ≤ t) :
    (analyticLeadingMatrix r hr (xOfT t)).det < 0 ↔ W r t < 0 := by
  rw [analyticLeadingMatrix_det_factor r hr t ht]
  exact mul_neg_iff_of_pos_left (analyticLeadingMatrix_det_factor_pos r hr t ht)

/-- Only the two already independently verified analytic/numeric
propositions remain as explicit arguments; no assumed congruence. -/
theorem mainClaim_of_transform_and_matrix
    (htransform : thetaTransformCorrect) (hmatrix : analyticMatrixPositive) :
    MainClaim := by
  intro t ht
  have hx := xOfT_positive_and_bounded t ht
  have h := hmatrix (xOfT t) hx.1 hx.2.le
  have hs :
      0 < (analyticLeadingMatrix 1 (by omega) (xOfT t)).det ∧
      (analyticLeadingMatrix 2 (by omega) (xOfT t)).det < 0 ∧
      (analyticLeadingMatrix 3 (by omega) (xOfT t)).det < 0 ∧
      0 < (analyticLeadingMatrix 4 (by omega) (xOfT t)).det ∧
      0 < (analyticLeadingMatrix 5 (by omega) (xOfT t)).det := by
    simpa only [analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
      htransform 1 (by omega) (xOfT t) hx.1 hx.2.le,
      analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
      htransform 2 (by omega) (xOfT t) hx.1 hx.2.le,
      analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
      htransform 3 (by omega) (xOfT t) hx.1 hx.2.le,
      analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
      htransform 4 (by omega) (xOfT t) hx.1 hx.2.le,
      analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
      htransform 5 (by omega) (xOfT t) hx.1 hx.2.le,
      thetaLeadingMatrix] using h
  exact ⟨(analyticLeadingMatrix_positive_iff_W 1 (by omega) t ht).mp hs.1,
    (analyticLeadingMatrix_negative_iff_W 2 (by omega) t ht).mp hs.2.1,
    (analyticLeadingMatrix_negative_iff_W 3 (by omega) t ht).mp hs.2.2.1,
    (analyticLeadingMatrix_positive_iff_W 4 (by omega) t ht).mp hs.2.2.2.1,
    (analyticLeadingMatrix_positive_iff_W 5 (by omega) t ht).mp hs.2.2.2.2⟩

#print axioms mainClaim_of_transform_and_matrix

end W5
