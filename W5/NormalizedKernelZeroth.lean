import W5.AnalyticTargets
import W5.ThetaIntegralStrictPositivity
import W5.ThetaInverseCoordinate

/-!
# Exact zeroth normalized coefficient of the ORIGINAL theta kernel

This module proves the first actual entry of the analytic normalized
Taylor coefficient matrix, rather than a surrogate or an assumed
coefficient transformation. At the theta coordinate x=xOfT(t),
its (0,0) entry is a strictly positive scalar multiple of the
original first Wronskian for every t >= 0.

This does NOT prove the required 2x2 through 5x5 determinant signs,
nor does it identify thetaCoefficient with analyticCoeff.
-/

namespace W5

/-- The explicit scalar multiplying the original theta tail in the
normalized two-variable kernel at u=v=0. -/
noncomputable def normalizationAtZero (x : ℝ) : ℝ :=
  let y : ℝ := 1 / x ^ (2 : ℕ)
  2 * Real.pi ^ ((1 : ℝ) / 4) * Real.exp y /
    y ^ ((5 : ℝ) / 4)

/-- The mixed Taylor coefficient of order (0,0) is the kernel value. -/
theorem analyticCoeff_zero_zero (x : ℝ) :
    analyticCoeff x (0 : Fin 5) (0 : Fin 5) =
      normalizedKernel x 0 0 := by
  simp [analyticCoeff]

/-- Exact normalization formula at the origin in both Taylor variables. -/
theorem normalizedKernel_zero_zero (x : ℝ) :
    normalizedKernel x 0 0 =
      normalizationAtZero x * Psi1 (thetaTimeOfX x) := by
  simp [normalizedKernel, normalizationAtZero, thetaTimeOfX]

/-- Genuine link between the (0,0) analytic matrix entry and
the original order-one Wronskian, with no sign hypothesis. -/
theorem analyticCoeff_zero_zero_xOfT (t : ℝ) :
    analyticCoeff (xOfT t) (0 : Fin 5) (0 : Fin 5) =
      normalizationAtZero (xOfT t) * W 1 t := by
  rw [analyticCoeff_zero_zero, normalizedKernel_zero_zero,
      thetaTimeOfX_xOfT, W_one_eq_Psi1]

/-- The normalizing scalar is strictly positive at any nonzero x. -/
theorem normalizationAtZero_pos (x : ℝ) (hx : x ≠ 0) :
    0 < normalizationAtZero x := by
  have hsq : 0 < x ^ (2 : ℕ) := sq_pos_of_ne_zero hx
  have hy : 0 < (1 : ℝ) / x ^ (2 : ℕ) := one_div_pos.mpr hsq
  unfold normalizationAtZero
  dsimp
  exact div_pos (by positivity) (Real.rpow_pos_of_pos hy _)

/-- Unconditional positivity of the actual first normalized
analytic coefficient on the entire t >= 0 ray. -/
theorem analyticCoeff_zero_zero_pos_on_ray (t : ℝ) (ht : 0 ≤ t) :
    0 < analyticCoeff (xOfT t) (0 : Fin 5) (0 : Fin 5) := by
  rw [analyticCoeff_zero_zero_xOfT]
  exact mul_pos
    (normalizationAtZero_pos (xOfT t) (ne_of_gt (xOfT_pos_all t)))
    (W_one_pos t ht)

end W5
