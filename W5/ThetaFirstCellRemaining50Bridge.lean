import W5.ThetaFirstCellBinomialMajorantSound
import W5.ThetaAudited51CellCertificateBridge

/-!
# One proved theta cell plus a generic checked residual chain

The first interval of the existing 51-cell rational partition is [0, 1/8].
The uniform real-theta first-cell certificate is now unconditional, and
its matrix passes the already formalized interval LDL checker.

We reuse the exact 255 rational pivot checks from the audited matrices
to obtain the 50 remaining finite checks by removing the first element.
No second numerical evaluation is needed.

The remaining analytical enclosure of the 50 genuine theta-matrix
intervals is an EXPLICIT premise. In particular, this theorem does not
establish the complete order-five conjecture.
-/

namespace W5

/-- The gamma/majorant certificate controls all 15 independent
entries of the actual first-cell theta matrix. -/
theorem thetaFirstCell_upperRealCertificate :
    ThetaUpperRealCellCertificate 0 (1 / 8 : ℚ) := by
  refine ⟨thetaFirstCellGammaUniformMatrix,
    thetaFirstCellGammaUniformMatrix_pivotSigns, ?_⟩
  intro x hx _ hxB i j _
  have hxb : x ≤ (1 : ℝ) / 8 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hxB
  exact thetaFirstCellGammaUniformMatrix_containsReal
    thetaFirstCellGammaUniformCoefficientBound_from_majorant x hx hxb i j

/-- The exact rational 51-cell partition begins at 1/8.
The rest of the partition is reused literally, without copying constants. -/
theorem theta_endpoints_first_eq_eighth :
    endpoints = (1 / 8 : ℚ) :: endpoints.drop 1 := by
  native_decide

/-- Generic composition: a proved first certificate and any
certified continuation give the full interval chain. -/
theorem thetaUpperChain_prepend
    (a b : ℚ) (bs : List ℚ)
    (hfirst : ThetaUpperRealCellCertificate a b)
    (htail : ThetaUpperRealCellCertificateChain b bs) :
    ThetaUpperRealCellCertificateChain a (b :: bs) := by
  exact ⟨hfirst, htail⟩

/-- The original global analytic sign target now requires at most
50 further analytical cell certificates, not 51. -/
theorem analyticMatrixPositive_of_remaining_50_upper_certificates
    (htail :
      ThetaUpperRealCellCertificateChain (1 / 8 : ℚ)
        (endpoints.drop 1)) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_51_upper_cell_certificates
  rw [theta_endpoints_first_eq_eighth]
  exact thetaUpperChain_prepend 0 (1 / 8 : ℚ) (endpoints.drop 1)
    thetaFirstCell_upperRealCertificate htail

/-- The exact-rational LDL checker for the remaining 50 matrices is
a logical consequence of the already compiled original 255 tests.
It never runs a second 250-pivot computation. -/
theorem thetaAuditRemaining50Matrices_checked :
    thetaCellMatricesCheck (endpoints.drop 1)
      (thetaAuditUpperCellMatrices.drop 1) = true := by
  have hall : thetaCellMatricesCheck endpoints
      thetaAuditUpperCellMatrices = true :=
    thetaAuditUpperCellMatrices_checked
  rw [theta_endpoints_first_eq_eighth] at hall
  change (intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals thetaAuditUpperCell_01) &&
      thetaCellMatricesCheck (endpoints.drop 1)
        (thetaAuditUpperCellMatrices.drop 1)) = true at hall
  simp only [Bool.and_eq_true] at hall
  exact hall.2

/-- Fully reusable 50-cell reduction using all the preexisting
rational matrices and pivot proofs. The only open hypothesis consists
of genuine uniform theta-entry enclosures on these 50 cells. -/
theorem analyticMatrixPositive_of_remaining_50_audited_enclosures
    (hreal : ThetaCellMatricesEnclose (1 / 8 : ℚ)
      (endpoints.drop 1) (thetaAuditUpperCellMatrices.drop 1)) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_50_upper_certificates
  exact thetaUpperRealCellCertificateChain_of_matrices
    (1 / 8 : ℚ) (endpoints.drop 1)
    (thetaAuditUpperCellMatrices.drop 1)
    thetaAuditRemaining50Matrices_checked hreal

end W5
