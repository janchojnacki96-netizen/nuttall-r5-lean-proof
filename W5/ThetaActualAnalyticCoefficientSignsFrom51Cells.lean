import W5.Theta51CellRealCertificateReduction

/-!
# Transfer the 51-cell theta certificate to genuine normalized-kernel derivatives

The previous module proves the five leading principal determinant signs
for `thetaCoefficient` assuming 51 certified interval cells. But the
quantity that is *defined by actual derivatives of normalizedKernel*
is `analyticCoeff`, not `thetaCoefficient`.

The equality of these two definitions is exactly the existing
`thetaTransformCorrect` analytic obligation. Here we make the transfer
precise and reusable for every matrix order r ≤ 5, without repeating
the Schur determinant or interval arithmetic proofs.

Neither the 51 cell certificates nor thetaTransformCorrect is assumed
unconditionally; both remain explicit premises.
-/

namespace W5

/-- Leading r×r block of the actual normalized-kernel Taylor coefficients. -/
noncomputable def analyticLeadingMatrix (r : ℕ) (hr : r ≤ 5) (x : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of (fun i j =>
    analyticCoeff x
      (⟨i.val, by omega⟩ : Fin 5)
      (⟨j.val, by omega⟩ : Fin 5))

/-- Leading r×r block of the closed theta integral/series coefficients. -/
noncomputable def thetaLeadingMatrix (r : ℕ) (hr : r ≤ 5) (x : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of (fun i j =>
    thetaCoefficient x
      (⟨i.val, by omega⟩ : Fin 5)
      (⟨j.val, by omega⟩ : Fin 5))

/-- All 25 analytic Taylor coefficients agree with their theta
series representations, if the exact analytic transformation is proved.
This is an equality of genuine real matrices, not just determinants. -/
theorem analyticLeadingMatrix_eq_thetaLeadingMatrix
    (htransform : thetaTransformCorrect)
    (r : ℕ) (hr : r ≤ 5) (x : ℝ)
    (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256) :
    analyticLeadingMatrix r hr x = thetaLeadingMatrix r hr x := by
  ext i j
  exact htransform x hx hbound
    (⟨i.val, by omega⟩ : Fin 5)
    (⟨j.val, by omega⟩ : Fin 5)

/-- Consequently the actual derivative-defined leading determinants
agree with the theta determinants, for EVERY order up to five. -/
theorem analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
    (htransform : thetaTransformCorrect)
    (r : ℕ) (hr : r ≤ 5) (x : ℝ)
    (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256) :
    (analyticLeadingMatrix r hr x).det =
      (thetaLeadingMatrix r hr x).det := by
  rw [analyticLeadingMatrix_eq_thetaLeadingMatrix
    htransform r hr x hx hbound]

/-- The exact derivative-defined normalized-kernel matrix has the
desired five leading principal minor signs, PROVIDED the 51 uniform
real theta interval certificates and thetaTransformCorrect are supplied.
The matrix here uses `iteratedDeriv` of `normalizedKernel` directly. -/
theorem analytic_all_five_minor_signs_of_51_cells
    (hcells : ThetaRealCellCertificateChain 0 endpoints)
    (htransform : thetaTransformCorrect)
    (x : ℝ) (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256) :
    0 < (analyticLeadingMatrix 1 (by omega) x).det ∧
      (analyticLeadingMatrix 2 (by omega) x).det < 0 ∧
      (analyticLeadingMatrix 3 (by omega) x).det < 0 ∧
      0 < (analyticLeadingMatrix 4 (by omega) x).det ∧
      0 < (analyticLeadingMatrix 5 (by omega) x).det := by
  have h := (analyticMatrixPositive_of_51_real_cell_certificates
    hcells) x hx hbound
  simpa only [analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
    htransform 1 (by omega) x hx hbound,
    analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
    htransform 2 (by omega) x hx hbound,
    analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
    htransform 3 (by omega) x hx hbound,
    analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
    htransform 4 (by omega) x hx hbound,
    analyticLeadingMatrix_det_eq_thetaLeadingMatrix_det
    htransform 5 (by omega) x hx hbound,
    thetaLeadingMatrix] using h

end W5
