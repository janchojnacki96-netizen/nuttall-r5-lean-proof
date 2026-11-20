import W5.ThetaActualNormalizedKernelCertificateSeries
import W5.ThetaGaussianIntegratedSeriesDerivative
import W5.ThetaCertificateBaseCorrectionSplit

/-!
# Reuse the EXISTING Gaussian integrated series for the original kernel

The verified analytic substitution path has produced
`thetaCertificateGaussianFullTerm` for the ORIGINAL normalized
Nuttall kernel. But the project already has an extensive calculus
library for a weighted transformed integral named
`thetaGaussianIntegratedSeriesTerm`.

These are the SAME correction integrals. This module identifies
them exactly, with the square-index factor canceled using the
previously proved `thetaCoefficient_cancel_square_index`.

This creates a *function-level* decomposition into an elementary
Gaussian base series and the existing integrated correction series.
We deliberately retain a SINGLE tsum of differences, since splitting
an infinite sum requires summability hypotheses, not merely algebra.

Consequently future higher-jet computations can reuse the existing
Mathlib-based differentiated integrated-series lemmas rather than
rebuild majorants or differentiation-under-integral arguments.
-/

namespace W5
open MeasureTheory

/-- Unintegrated Gaussian contribution to the actual, original,
two-variable normalized theta kernel at square index n. -/
noncomputable def thetaCertificateGaussianBaseTerm
    (x u v : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (n:ℝ)^2 * Real.exp (-((n:ℝ)^2-1)/x^2) *
      thetaGaussianModel (((n:ℝ)^2-1)/x) ((n:ℝ)^2) u v

/-- Exact equality of the ORIGINAL n-th gamma-derived kernel term
with the elementary Gaussian base term MINUS the same weighted
integral already differentiated in the earlier analytic modules.
No series operation, derivative or Fubini interchange occurs. -/
theorem thetaCertificateGaussianFullTerm_eq_base_sub_integrated
    (x u v : ℝ) (n : ℕ) :
    thetaCertificateGaussianFullTerm x u v n =
      thetaCertificateGaussianBaseTerm x u v n -
        (x^2/4) * thetaGaussianIntegratedSeriesTerm x u n v := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateGaussianFullTerm,
      thetaCertificateGaussianBaseTerm, thetaGaussianIntegratedSeriesTerm]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnreal : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hp : ((n:ℝ)^2) ≠ 0 := by positivity
    simp only [thetaCertificateGaussianFullTerm,
      thetaCertificateGaussianBaseTerm,
      thetaGaussianIntegratedSeriesTerm, if_neg hn]
    change
      ((n:ℝ)^2) * Real.exp (-((n:ℝ)^2-1)/x^2) *
        (thetaGaussianModel (((n:ℝ)^2-1)/x) ((n:ℝ)^2) u v -
          (x^2/(4*((n:ℝ)^2))) *
            (∫ w : ℝ, thetaWeightedGaussianIntegrand
              x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v w
              ∂(volume.restrict (Set.Ioi (0:ℝ))))) =
      ((n:ℝ)^2) * Real.exp (-((n:ℝ)^2-1)/x^2) *
        thetaGaussianModel (((n:ℝ)^2-1)/x) ((n:ℝ)^2) u v -
        (x^2/4) *
          (Real.exp (-((n:ℝ)^2-1)/x^2) *
            (∫ w : ℝ, thetaWeightedGaussianIntegrand
              x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v w
              ∂(volume.restrict (Set.Ioi (0:ℝ)))))
    simpa only [mul_assoc] using
      (thetaCoefficient_cancel_square_index
        x ((n:ℝ)^2) (Real.exp (-((n:ℝ)^2-1)/x^2))
        (thetaGaussianModel (((n:ℝ)^2-1)/x) ((n:ℝ)^2) u v)
        (∫ w : ℝ, thetaWeightedGaussianIntegrand
          x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) hp)

/-- The original kernel is a single exact sum of the elementary
Gaussian terms minus the EXISTING integrated Gaussian correction.
This does not yet split the sum: we do not assume its two components
are independently summable on the full local patch. -/
theorem normalizedKernel_eq_base_sub_existing_integrated_series
    (x u v : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    normalizedKernel x u v =
      ∑' n : ℕ,
        (thetaCertificateGaussianBaseTerm x u v n -
          (x^2/4) * thetaGaussianIntegratedSeriesTerm x u n v) := by
  rw [normalizedKernel_eq_thetaCertificateGaussianFullSeries
    x u v hx hxB hu hv]
  apply tsum_congr
  intro n
  exact thetaCertificateGaussianFullTerm_eq_base_sub_integrated x u v n

end W5
