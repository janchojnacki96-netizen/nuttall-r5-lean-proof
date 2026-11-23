import W5.ThetaSecondCellRemaining49Reduction
import W5.ThetaThirdCellAllFiveSigns

/-!
# Three TRUE theta cells; the residual numerical proof is now 48 cells

The third cell is not a hypothetical interval. Its genuine n=1
cubic-Gamma matrix, real n=2,3,4 signed-series term bounds, and actual
n>=5 Gaussian tail have passed independent Lean CI.

Re-use the old exactly checked 51-cell 768-bit LDL output without
repeating the costly 240-pivot computation.
-/

namespace W5

/-- A checked real-semantic upper-triangle interval certificate for
the complete original third theta cell, 177/512 <= x <= 821/2048. -/
theorem thetaThirdCell_upperRealCertificate :
    ThetaUpperRealCellCertificate (177/512:ℚ) (821/2048:ℚ) := by
  refine ⟨thetaThirdCellCubicWidenedMatrix,
    thetaThirdCellCubicWidenedMatrix_pivotSigns, ?_⟩
  intro x hx hax hxb i j hij
  have ha : (177:ℝ)/512 ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hax
  have hb : x ≤ (821:ℝ)/2048 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hxb
  have htail : ∀ k l : Fin 5,
      |thetaAuditedTail 2 x k l| ≤ (1:ℝ)/100 := by
    intro k l
    exact thetaThirdCell_tail_two_abs_le_oneHundred x ha hb k l
  change QInterval.ContainsReal
    (thetaGeneralCellCubicWidenedMatrix (177/512) (821/2048) i j)
    (thetaCoefficient x i j)
  exact thetaGeneralCellCubicWidenedMatrix_containsReal_of_tail
    (177/512) (821/2048) x
    (by norm_num) hx hax hxb (by norm_num) htail i j

/-- The third interval endpoint is the actual original auditor
rational endpoint, not an adjusted or floating-point approximation. -/
theorem theta_endpoints_third :
    endpoints.drop 2 =
      (821/2048:ℚ) :: endpoints.drop 3 :=
  thetaThirdCell_endpoint

/-- Reuse three genuine-theta cells. Exactly 48 further REAL
upper-triangle interval certificates remain to prove. -/
theorem analyticMatrixPositive_of_remaining_48_upper_certificates
    (h48 : ThetaUpperRealCellCertificateChain
      (821/2048:ℚ) (endpoints.drop 3)) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_49_upper_certificates
  rw [theta_endpoints_third]
  exact ⟨thetaThirdCell_upperRealCertificate, h48⟩

/-- Extract the third Boolean pivot test from the original 49-cell
chain. All 48 remaining *fixed 768-bit* rational LDL tests are
already checked: no recomputation of the original pivot data. -/
theorem thetaAuditRemaining48Matrices_checked :
    thetaCellMatricesCheck (endpoints.drop 3)
      (thetaAuditUpperCellMatrices.drop 3) = true := by
  have h49 := thetaAuditRemaining49Matrices_checked
  have hMat : thetaAuditUpperCellMatrices.drop 2 =
      thetaAuditUpperCell_03 :: thetaAuditUpperCellMatrices.drop 3 := by
    rfl
  rw [theta_endpoints_third, hMat] at h49
  change (intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals thetaAuditUpperCell_03) &&
      thetaCellMatricesCheck (endpoints.drop 3)
        (thetaAuditUpperCellMatrices.drop 3)) = true at h49
  simp only [Bool.and_eq_true] at h49
  exact h49.2

/-- The alternate path through the original 48 audited matrices:
only the 48 TRUE real entrywise enclosures remain open. -/
theorem analyticMatrixPositive_of_remaining_48_audited_enclosures
    (h48 : ThetaCellMatricesEnclose (821/2048:ℚ)
      (endpoints.drop 3) (thetaAuditUpperCellMatrices.drop 3)) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_48_upper_certificates
  exact thetaUpperRealCellCertificateChain_of_matrices
    (821/2048:ℚ) (endpoints.drop 3)
    (thetaAuditUpperCellMatrices.drop 3)
    thetaAuditRemaining48Matrices_checked h48

end W5
