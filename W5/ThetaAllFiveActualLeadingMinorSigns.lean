import W5.LeadingThreeFourRealLDLDeterminants
import W5.ThetaActualLeadingMinorOneTwoFromPivots

/-!
# ALL five original theta leading determinant signs from ONE interval certificate

The real interval LDL checker already supplies five alternating signs
for the actual 5×5 thetaCoefficient matrix. Earlier verified theorems
proved:
* leading size 1 and 2 determinant signs directly;
* generic Mathlib Schur determinant factorization;
* the equality between full-real-LDL pivots and the Schur pivots;
* the leading 3, 4, and 5 determinant/product identities.

This file *only composes* those results. It does NOT use a
single-Gaussian proxy: every matrix entry is the original actual
thetaCoefficient including its infinite theta sum/integral correction.

Remaining hypotheses are explicit: rational intervals must enclose
the true theta values, and exact rational interval pivot checks
must pass at each x. These are not supplied here.
-/

namespace W5

/-- The ORIGINAL leading 3×3 theta matrix, not a surrogate. -/
noncomputable def thetaMatrixThree (x : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun i j : Fin 3 =>
    thetaCoefficient x (⟨i.val, by omega⟩ : Fin 5)
      (⟨j.val, by omega⟩ : Fin 5))

/-- The ORIGINAL leading 4×4 theta matrix, not a surrogate. -/
noncomputable def thetaMatrixFour (x : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun i j : Fin 4 =>
    thetaCoefficient x (⟨i.val, by omega⟩ : Fin 5)
      (⟨j.val, by omega⟩ : Fin 5))

/-- The exact original theta 3×3 leading determinant is strictly
negative under real entry enclosures and five interval checks. -/
theorem thetaMatrixThree_det_negative_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    (thetaMatrixThree x).det < 0 := by
  have hp := thetaFive_pivotSigns_of_interval x B hentry hchecks
  have h0 :
      (realLDL5 (originalThetaMatrixFive x) 0)
        (pivotIndexFive 0) (pivotIndexFive 0) ≠ 0 := by
    change originalThetaRealPivot x 0 ≠ 0
    exact ne_of_gt hp.1
  have h1 :
      (realLDL5 (originalThetaMatrixFive x) 1)
        (pivotIndexFive 1) (pivotIndexFive 1) ≠ 0 := by
    change originalThetaRealPivot x 1 ≠ 0
    exact ne_of_lt hp.2.1
  change (leadingRealThree (originalThetaMatrixFive x)).det < 0
  rw [det_leading_three_eq_realLDL5_product
    (originalThetaMatrixFive x) h0 h1]
  change originalThetaRealPivot x 0 *
    originalThetaRealPivot x 1 *
    originalThetaRealPivot x 2 < 0
  exact (thetaFive_productSigns_of_interval x B hentry hchecks).2.2.1

/-- The exact original theta 4×4 leading determinant is strictly
positive under the SAME real interval certificate. -/
theorem thetaMatrixFour_det_positive_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    0 < (thetaMatrixFour x).det := by
  have hp := thetaFive_pivotSigns_of_interval x B hentry hchecks
  have h0 :
      (realLDL5 (originalThetaMatrixFive x) 0)
        (pivotIndexFive 0) (pivotIndexFive 0) ≠ 0 := by
    change originalThetaRealPivot x 0 ≠ 0
    exact ne_of_gt hp.1
  have h1 :
      (realLDL5 (originalThetaMatrixFive x) 1)
        (pivotIndexFive 1) (pivotIndexFive 1) ≠ 0 := by
    change originalThetaRealPivot x 1 ≠ 0
    exact ne_of_lt hp.2.1
  have h2 :
      (realLDL5 (originalThetaMatrixFive x) 2)
        (pivotIndexFive 2) (pivotIndexFive 2) ≠ 0 := by
    change originalThetaRealPivot x 2 ≠ 0
    exact ne_of_gt hp.2.2.1
  change 0 < (leadingRealFour (originalThetaMatrixFive x)).det
  rw [det_leading_four_eq_realLDL5_product
    (originalThetaMatrixFive x) h0 h1 h2]
  change 0 < originalThetaRealPivot x 0 *
    originalThetaRealPivot x 1 *
    originalThetaRealPivot x 2 *
    originalThetaRealPivot x 3
  exact (thetaFive_productSigns_of_interval x B hentry hchecks).2.2.2.1

/-- All five signs of the ACTUAL original theta coefficient matrix
follow from a single precise real interval certificate. -/
theorem theta_all_five_minor_signs_of_interval
    (x : ℝ) (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B) :
    0 < (thetaMatrixOne x).det ∧
      (thetaMatrixTwo x).det < 0 ∧
      (thetaMatrixThree x).det < 0 ∧
      0 < (thetaMatrixFour x).det ∧
      0 < (originalThetaMatrixFive x).det := by
  exact ⟨thetaMatrixOne_det_positive_of_interval x B hentry hchecks,
    thetaMatrixTwo_det_negative_of_interval x B hentry hchecks,
    thetaMatrixThree_det_negative_of_interval x B hentry hchecks,
    thetaMatrixFour_det_positive_of_interval x B hentry hchecks,
    originalThetaMatrixFive_det_positive_of_interval x B hentry hchecks⟩

/-- Isolate the remaining interval-analytic obligation for the
whole permitted x-range. Producing a rigorous interval matrix at
each x, with finite certified pivot signs, would discharge the
existing `analyticMatrixPositive` proposition WITHOUT another
determinant or linear-algebra proof. -/
theorem analyticMatrixPositive_of_real_interval_family
    (hfamily : ∀ x : ℝ, 0 < x → x ≤ (145 : ℝ) / 256 →
      ∃ B : Matrix (Fin 5) (Fin 5) QInterval,
        (∀ i j : Fin 5,
          QInterval.ContainsReal (B i j) (thetaCoefficient x i j)) ∧
        intervalLDL5Alternating B) :
    analyticMatrixPositive := by
  intro x hx hbound
  obtain ⟨B, hentry, hchecks⟩ := hfamily x hx hbound
  have h := theta_all_five_minor_signs_of_interval
    x B hentry hchecks
  simpa [thetaMatrixOne, thetaMatrixTwo, thetaMatrixThree,
    thetaMatrixFour, originalThetaMatrixFive] using h

end W5
