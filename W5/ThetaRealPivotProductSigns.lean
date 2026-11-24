import W5.VerifiedIntervalRealLDL5
import W5.FiniteCore

/-!
# Signed REAL theta LDL pivots imply all five product-sign targets

Mathlib/rational interval soundness (PR #95) gives five individual
strict pivot signs for the ORIGINAL real theta coefficient matrix.
The project already has the exact ordered-field lemma
`productSigns_of_pivotSigns`. Reuse it to package all five
cumulative pivot products with the Nuttall sign sequence.

The pivot products are algebraic quantities naturally matched
to leading principal determinants by the Schur determinant identity
`Matrix.det_fromBlocks₁₁`. That determinant/pivot equality is
a separate remaining goal and is NOT assumed or claimed here.

The only premises remain explicit: entrywise certified rational
enclosures of all 25 real theta coefficients, and five exact
interval pivot sign checks. No new numerical values or signs
of the ACTUAL theta determinants are postulated.
-/

namespace W5

/-- Exact kth Schur pivot of the ORIGINAL real theta coefficient
matrix, using the verified five-stage elimination. -/
noncomputable def originalThetaRealPivot
    (x : ℝ) (k : Fin 5) : ℝ :=
  (realLDL5 (originalThetaMatrixFive x) k.val)
    (pivotIndexFive k.val) (pivotIndexFive k.val)

/-- A single finite interval certificate on the 5x5 ORIGINAL
theta matrix proves ALL five real pivot signs at once. -/
theorem thetaFive_pivotSigns_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    PivotSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) := by
  have h0 : 0 < originalThetaRealPivot x 0 := by
    simpa [originalThetaRealPivot] using
      (thetaCertificateFive_real_pivot_signs_of_interval
        x B hentry hchecks 0 (by omega))
  have h1 : originalThetaRealPivot x 1 < 0 := by
    simpa [originalThetaRealPivot] using
      (thetaCertificateFive_real_pivot_signs_of_interval
        x B hentry hchecks 1 (by omega))
  have h2 : 0 < originalThetaRealPivot x 2 := by
    simpa [originalThetaRealPivot] using
      (thetaCertificateFive_real_pivot_signs_of_interval
        x B hentry hchecks 2 (by omega))
  have h3 : originalThetaRealPivot x 3 < 0 := by
    simpa [originalThetaRealPivot] using
      (thetaCertificateFive_real_pivot_signs_of_interval
        x B hentry hchecks 3 (by omega))
  have h4 : 0 < originalThetaRealPivot x 4 := by
    simpa [originalThetaRealPivot] using
      (thetaCertificateFive_real_pivot_signs_of_interval
        x B hentry hchecks 4 (by omega))
  exact ⟨h0, h1, h2, h3, h4⟩

/-- Reuse the already verified W5 ordered-field sign-product lemma,
instead of repeating any multiplication sign case. -/
theorem thetaFive_productSigns_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    ProductSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) := by
  exact productSigns_of_pivotSigns
    (thetaFive_pivotSigns_of_interval x B hentry hchecks)

end W5
