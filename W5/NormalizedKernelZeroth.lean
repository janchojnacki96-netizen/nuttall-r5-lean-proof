import W5.AnalyticTargets
import W5.ThetaIntegralStrictPositivity
import W5.ThetaInverseCoordinate
import W5.PositiveScalarCongruence

/-!
# Exact zeroth normalized coefficient of the ORIGINAL theta kernel

This module proves the first actual entry of the analytic normalized
Taylor coefficient matrix, rather than a surrogate or an assumed
coefficient transformation. At the theta coordinate x=xOfT(t),
its (0,0) entry is precisely the existing positive kernelNormalization
times the ORIGINAL Wronskian W 1 t.

This does NOT prove the required 2x2 through 5x5 determinant signs,
nor does it identify thetaCoefficient with analyticCoeff.
-/

namespace W5

/-- The mixed Taylor coefficient of order (0,0) is the kernel value. -/
theorem analyticCoeff_zero_zero (x : ℝ) :
    analyticCoeff x (0 : Fin 5) (0 : Fin 5) =
      normalizedKernel x 0 0 := by
  simp [analyticCoeff]

/-- Exact normalization formula at the origin in both Taylor variables.
The scalar here is exactly the pre-existing kernelNormalization used
in the matrix-congruence formalization. -/
theorem normalizedKernel_zero_zero (x : ℝ) :
    normalizedKernel x 0 0 =
      kernelNormalization x * Psi1 (thetaTimeOfX x) := by
  simp [normalizedKernel, kernelNormalization, thetaTimeOfX]

/-- Genuine link between the (0,0) analytic matrix entry and
the original order-one Wronskian, with no sign hypothesis. -/
theorem analyticCoeff_zero_zero_xOfT (t : ℝ) :
    analyticCoeff (xOfT t) (0 : Fin 5) (0 : Fin 5) =
      kernelNormalization (xOfT t) * W 1 t := by
  rw [analyticCoeff_zero_zero, normalizedKernel_zero_zero,
      thetaTimeOfX_xOfT, W_one_eq_Psi1]

/-- Unconditional positivity of the actual first normalized
analytic coefficient on the entire t >= 0 ray. -/
theorem analyticCoeff_zero_zero_pos_on_ray (t : ℝ) (ht : 0 ≤ t) :
    0 < analyticCoeff (xOfT t) (0 : Fin 5) (0 : Fin 5) := by
  rw [analyticCoeff_zero_zero_xOfT]
  exact mul_pos
    (kernelNormalization_pos (xOfT t) ((xOfT_positive_and_bounded t ht).1))
    (W_one_pos t ht)

end W5
