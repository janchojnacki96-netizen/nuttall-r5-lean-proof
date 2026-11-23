import W5.ThetaFirstCellRemaining50Bridge
import W5.ThetaSecondCellHeadAllFiveSigns

/-!
# Two unconditional theta cells: reduce the analytic certificate to 49 cells

The first x-cell [0,1/8] was certified in the existing first-cell Gamma
proof. The entire second x-cell [1/8,177/512] now has unconditional genuine
real-theta n=2,3 bounds and a checked widened LDL interval matrix.

This file puts the second result into the *existing upper-triangle
certificate interface*, then removes TWO front cells from the previously
verified 51-cell chain. The original exact 768-bit LDL checks for the
remaining 49 matrices are inherited from the old 50-cell Boolean result.

Only the 49 residual genuine real-theta interval enclosures are assumed.
The 24 original normalized-kernel mixed jet identifications and final
Wronskian transport are additional distinct open tasks.
-/

namespace W5

/-- The actual original theta coefficient matrix is uniformly enclosed
by the independently checked widened cubic-Gamma LDL matrix on x-cell 2.
This is a genuine real enclosure, not a numerical proxy. -/
theorem thetaSecondCell_upperRealCertificate :
    ThetaUpperRealCellCertificate (1/8 : ℚ) (177/512 : ℚ) := by
  refine ⟨thetaSecondCellCubicWidenedMatrix,
    thetaSecondCellCubicWidenedMatrix_pivotSigns, ?_⟩
  intro x hx hax hxb i j hij
  have ha : (1:ℝ)/8 ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hax
  have hb : x ≤ (177:ℝ)/512 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hxb
  obtain ⟨h2, h3⟩ :=
    thetaSecondCell_unconditional_two_three_abs_bounds x ha hb
  have htail : ∀ k l : Fin 5,
      |thetaAuditedTail 2 x k l| ≤ (1:ℝ)/100 := by
    intro k l
    exact (thetaSecondCell_tail_two_abs_lt_oneHundred
      x ha hb k l (h2 k l) (h3 k l)).le
  exact thetaSecondCellCubicWidenedMatrix_containsReal_of_tail
    x ha hb htail i j

/-- Verify the imported 51-cell partition starts with exactly the
two independently proven analytic ranges, without approximating endpoints. -/
theorem theta_endpoints_first_two :
    endpoints = (1/8:ℚ) :: (177/512:ℚ) :: endpoints.drop 2 := by
  native_decide

/-- The original theta five-minor sign theorem now requires only
49 remaining genuine upper-triangle cell certificates, not 51. -/
theorem analyticMatrixPositive_of_remaining_49_upper_certificates
    (h49 : ThetaUpperRealCellCertificateChain
      (177/512 : ℚ) (endpoints.drop 2)) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_51_upper_cell_certificates
  rw [theta_endpoints_first_two]
  exact ⟨thetaFirstCell_upperRealCertificate,
    thetaSecondCell_upperRealCertificate, h49⟩

/-- Reuse the already proved exact rational LDL result for the remaining
50 original auditor matrices: the tail of a true Boolean conjunction
is true, so no new 245-pivot computation is needed. -/
theorem thetaAuditRemaining49Matrices_checked :
    thetaCellMatricesCheck (endpoints.drop 2)
      (thetaAuditUpperCellMatrices.drop 2) = true := by
  have h50 := thetaAuditRemaining50Matrices_checked
  have hEnd : endpoints.drop 1 =
      (177/512:ℚ) :: endpoints.drop 2 := by
    native_decide
  have hMat : thetaAuditUpperCellMatrices.drop 1 =
      thetaAuditUpperCell_02 :: thetaAuditUpperCellMatrices.drop 2 := by
    rfl
  rw [hEnd, hMat] at h50
  change (intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals thetaAuditUpperCell_02) &&
      thetaCellMatricesCheck (endpoints.drop 2)
        (thetaAuditUpperCellMatrices.drop 2)) = true at h50
  exact (Bool.and_eq_true.mp h50).2

/-- Single final real-semantic obligation for the 49 imported 768-bit
interval matrices. Their exact rational LDL signs, the first two
actual theta cells, and the full 51-cell coverage are already proved. -/
theorem analyticMatrixPositive_of_remaining_49_audited_enclosures
    (h49 : ThetaCellMatricesEnclose (177/512 : ℚ)
      (endpoints.drop 2) (thetaAuditUpperCellMatrices.drop 2)) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_49_upper_certificates
  exact thetaUpperRealCellCertificateChain_of_matrices
    (177/512 : ℚ) (endpoints.drop 2)
    (thetaAuditUpperCellMatrices.drop 2)
    thetaAuditRemaining49Matrices_checked h49

end W5
