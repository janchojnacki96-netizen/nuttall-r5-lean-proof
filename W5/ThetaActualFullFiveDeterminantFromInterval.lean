import W5.RealLDL5PivotSchurIdentification
import W5.ThetaRealPivotProductSigns

/-!
# Genuine full 5×5 theta determinant sign from a verified real interval certificate

Mathlib's Schur determinant factorization has now been connected to the
very same five REAL pivot values computed by `realLDL5`.
The existing formally verified rational interval checker transports the
five alternating pivot signs to the ORIGINAL `thetaCoefficient` matrix.

This module composes those results. Given only:
1. entrywise rigorously certified real enclosures of the 25 theta values;
2. five successful rational interval pivot sign tests;
it proves the actual full theta matrix determinant strictly positive.

Neither hypothesis is silently assumed: the transcendental interval
enclosures and their concrete endpoint data still need to be supplied.
There is no numerical surrogate, fabricated sign, or new axiom.
-/

namespace W5

/-- Strict positive determinant of the ACTUAL full 5×5 theta matrix,
conditional precisely on sound entry enclosures and checked rational
pivot signs. The determinant sign is *derived*, not assumed. -/
theorem originalThetaMatrixFive_det_positive_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    0 < (originalThetaMatrixFive x).det := by
  have hp := thetaFive_pivotSigns_of_interval x B hentry hchecks
  rcases hp with ⟨hp0, hp1, hp2, hp3, _⟩
  have h0 :
      (realLDL5 (originalThetaMatrixFive x) 0)
        (pivotIndexFive 0) (pivotIndexFive 0) ≠ 0 := by
    change originalThetaRealPivot x 0 ≠ 0
    exact ne_of_gt hp0
  have h1 :
      (realLDL5 (originalThetaMatrixFive x) 1)
        (pivotIndexFive 1) (pivotIndexFive 1) ≠ 0 := by
    change originalThetaRealPivot x 1 ≠ 0
    exact ne_of_lt hp1
  have h2 :
      (realLDL5 (originalThetaMatrixFive x) 2)
        (pivotIndexFive 2) (pivotIndexFive 2) ≠ 0 := by
    change originalThetaRealPivot x 2 ≠ 0
    exact ne_of_gt hp2
  have h3 :
      (realLDL5 (originalThetaMatrixFive x) 3)
        (pivotIndexFive 3) (pivotIndexFive 3) ≠ 0 := by
    change originalThetaRealPivot x 3 ≠ 0
    exact ne_of_lt hp3
  rw [det_five_eq_realLDL5_pivot_product
    (originalThetaMatrixFive x) h0 h1 h2 h3]
  change 0 <
    originalThetaRealPivot x 0 *
      originalThetaRealPivot x 1 *
      originalThetaRealPivot x 2 *
      originalThetaRealPivot x 3 *
      originalThetaRealPivot x 4
  exact (thetaFive_productSigns_of_interval
    x B hentry hchecks).2.2.2.2

/-- The same result in the matrix notation used by
`analyticMatrixPositive`, without introducing an alternate
numerical matrix definition. -/
theorem thetaMatrixFive_det_positive_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    0 < (Matrix.of (fun (i j : Fin 5) =>
      thetaCoefficient x i j)).det := by
  exact originalThetaMatrixFive_det_positive_of_interval
    x B hentry hchecks

end W5
