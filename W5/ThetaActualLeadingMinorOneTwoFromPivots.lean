import W5.ThetaRealPivotProductSigns
import W5.OrderTwoThetaCertificateBridge

/-!
# Signs of the ACTUAL theta leading principal minors of sizes one and two

The previously kernel-verified interval checker (#95-#96) proves strict
signs of all five REAL Schur pivots of the ORIGINAL thetaCoefficient
matrix, provided real theta entry enclosures and five finite interval
checks are supplied.

Here we discharge the determinant/pivot identity for the first two
leading principal minors, without guessing or assuming matrix signs.

Mathlib's ready-made `Matrix.det_fin_one` and `Matrix.det_fin_two`
make these cases exact. No new combinatorial determinant formula or
Schur reindexing infrastructure is required for orders one and two.

The remaining size-three through size-five determinant/pivot identities
must be proved separately, likely via Mathlib's general
`Matrix.det_fromBlocks₁₁` and block reindexing. All numerical entry
enclosures also remain explicit hypotheses.
-/

namespace W5

/-- The one-by-one leading principal block of the original theta
certificate; it contains the actual thetaCoefficient x 0 0. -/
noncomputable def thetaMatrixOne (x : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of (fun i j : Fin 1 =>
    thetaCoefficient x
      (⟨i.val, by omega⟩ : Fin 5)
      (⟨j.val, by omega⟩ : Fin 5))

/-- The original leading 1x1 theta determinant equals the FIRST
real elimination pivot exactly. No sign assumption is used. -/
theorem thetaMatrixOne_det_eq_first_pivot (x : ℝ) :
    (thetaMatrixOne x).det = originalThetaRealPivot x 0 := by
  rw [Matrix.det_fin_one]
  rfl

/-- The original leading 2x2 theta determinant equals the
product of the first two TRUE real elimination pivots whenever
the first pivot is nonzero.

This is a specialized Mathlib 2x2 determinant calculation:
  a*d-b*c = a*(d-c*b/a).
It does NOT refer to the single-n Gaussian determinant. -/
theorem thetaMatrixTwo_det_eq_first_two_pivots
    (x : ℝ) (ha : originalThetaRealPivot x 0 ≠ 0) :
    (thetaMatrixTwo x).det =
      originalThetaRealPivot x 0 * originalThetaRealPivot x 1 := by
  rw [Matrix.det_fin_two]
  change
    thetaCoefficient x 0 0 * thetaCoefficient x 1 1 -
      thetaCoefficient x 0 1 * thetaCoefficient x 1 0 =
    thetaCoefficient x 0 0 *
      (thetaCoefficient x 1 1 -
        thetaCoefficient x 1 0 * thetaCoefficient x 0 1 /
          thetaCoefficient x 0 0)
  have ha0 : thetaCoefficient x 0 0 ≠ 0 := by
    change thetaCoefficient x 0 0 ≠ 0 at ha
    exact ha
  field_simp [ha0] <;> ring

/-- A single interval certificate now proves the sign of the
ACTUAL theta 1x1 determinant, without postulating the sign. -/
theorem thetaMatrixOne_det_positive_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    0 < (thetaMatrixOne x).det := by
  rw [thetaMatrixOne_det_eq_first_pivot]
  exact (thetaFive_pivotSigns_of_interval x B hentry hchecks).1

/-- A single interval certificate also proves the strict
NEGATIVE determinant of the full infinite-series-corrected
ORIGINAL theta 2x2 leading block. The genuine numerical
theta coefficients are used, not one single Gaussian term. -/
theorem thetaMatrixTwo_det_negative_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    (thetaMatrixTwo x).det < 0 := by
  have hproducts :=
    thetaFive_productSigns_of_interval x B hentry hchecks
  have hfirst : 0 < originalThetaRealPivot x 0 := hproducts.1
  rw [thetaMatrixTwo_det_eq_first_two_pivots x (ne_of_gt hfirst)]
  exact hproducts.2.1

/-- Combined real theta order-one and order-two determinant signs,
conditional only on genuine theta entry enclosures and a successful
five-pivot rational interval check. -/
theorem thetaMatrix_one_two_signs_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    0 < (thetaMatrixOne x).det ∧
      (thetaMatrixTwo x).det < 0 := by
  exact ⟨thetaMatrixOne_det_positive_of_interval x B hentry hchecks,
    thetaMatrixTwo_det_negative_of_interval x B hentry hchecks⟩

end W5
