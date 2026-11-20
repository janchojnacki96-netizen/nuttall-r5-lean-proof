import W5.ThetaAudited51CellCertificateBridge
import W5.ThetaActualAnalyticCoefficientSignsFrom51Cells
import W5.ThetaActualAnalyticZeroZeroIdentification
import W5.ThetaOriginalKernelAllMixedJetsFromLocalEqOn
import W5.ThetaOriginalKernelExistingIntegratedSeries

/-!
# One audited-certificate-to-original-kernel bridge

Do not re-prove any interval LDL, 51-cell coverage, analytic kernel
gamma substitution, or Taylor-jet transport theorem. Instead, compose
the already CI-green theorems from PRs #114, #115, #116, #117, #125,
and #128/#129 in a single shared proof target.

Two SEPARATE hard obligations remain:
(1) ThetaCellMatricesEnclose for all 51 imported 768-bit matrices;
(2) equality of the remaining 24 normalized-kernel Gaussian-series
    Taylor jets and the original theta certificate coefficients.

The (0,0) equality is already unconditionally proved in PR #114.
No unconditional R5 assertion is made in this file.
-/

namespace W5

/-- One of the 25 original kernel/certificate coefficient equalities
was already proved in #114. Transport it to the series-jet interface
from #115 rather than repeating the analytic calculation. -/
theorem thetaCertificateGaussianAnalyticCoeff_zero_zero_eq_theta
    (x : ℝ) (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256) :
    thetaCertificateGaussianAnalyticCoeff x (0 : Fin 5) (0 : Fin 5) =
      thetaCoefficient x (0 : Fin 5) (0 : Fin 5) := by
  calc
    thetaCertificateGaussianAnalyticCoeff x 0 0 =
        analyticCoeff x 0 0 :=
      (analyticCoeff_eq_thetaCertificateGaussianAnalyticCoeff
        x hx hbound 0 0).symm
    _ = thetaCoefficient x 0 0 :=
      analyticCoeff_zero_zero_eq_thetaCoefficient x hx hbound

/-- For the original normalized Nuttall kernel's 5x5 coefficients,
it suffices to prove the 24 as-yet-unproved Gaussian-series jet
identities; the (0,0) case is filled by the EXISTING theorem #114. -/
theorem thetaTransformCorrect_of_remaining_24_gaussian_jets
    (hother :
      ∀ x : ℝ, 0 < x → x ≤ (145 : ℝ) / 256 →
        ∀ i j : Fin 5, (i ≠ 0 ∨ j ≠ 0) →
          thetaCertificateGaussianAnalyticCoeff x i j =
            thetaCoefficient x i j) :
    thetaTransformCorrect := by
  intro x hx hbound i j
  rw [analyticCoeff_eq_thetaCertificateGaussianAnalyticCoeff
    x hx hbound i j]
  by_cases h00 : i = 0 ∧ j = 0
  · rcases h00 with ⟨rfl, rfl⟩
    exact thetaCertificateGaussianAnalyticCoeff_zero_zero_eq_theta
      x hx hbound
  · have hnonzero : i ≠ 0 ∨ j ≠ 0 := by tauto
    exact hother x hx hbound i j hnonzero

/-- Directly connect the 255 actual Lean-verified rational pivot
certificates to the determinant signs of the ORIGINAL normalized
Nuttall kernel, relying on the PREVIOUS #117 theorem for the
analytic Taylor-matrix transport. Both missing analytical inputs
are explicit premises, never introduced as postulates. -/
theorem normalizedKernel_all_five_minor_signs_of_audited_768bit
    (hreal : ThetaCellMatricesEnclose 0 endpoints
      thetaAuditUpperCellMatrices)
    (htransform : thetaTransformCorrect)
    (x : ℝ) (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256) :
    0 < (analyticLeadingMatrix 1 (by omega) x).det ∧
      (analyticLeadingMatrix 2 (by omega) x).det < 0 ∧
      (analyticLeadingMatrix 3 (by omega) x).det < 0 ∧
      0 < (analyticLeadingMatrix 4 (by omega) x).det ∧
      0 < (analyticLeadingMatrix 5 (by omega) x).det := by
  have hupper : ThetaUpperRealCellCertificateChain 0 endpoints :=
    thetaUpperRealCellCertificateChain_of_matrices
      0 endpoints thetaAuditUpperCellMatrices
      thetaAuditUpperCellMatrices_checked hreal
  have hcells : ThetaRealCellCertificateChain 0 endpoints :=
    thetaRealCellCertificateChain_of_upper
      endpoints 0 hupper
  exact analytic_all_five_minor_signs_of_51_cells
    hcells htransform x hx hbound

end W5
