import W5.NormalizedKernelZeroth
import W5.PositiveScalarCongruence
import W5.PsiFundamentalDerivative
import W5.Range

/-!
# The exact order-two algebraic normalization factor

The zeroth normalized Taylor coefficient has already been identified
unconditionally with the original theta tail. At order two, the
remaining analytic tasks are the three nonconstant Taylor coefficients
(0,1), (1,0), and (1,1). This module records their precise formulas and
proves the resulting determinant identity *without* a numerical sign
assumption.

The formulas for these three analytic coefficients are hypotheses here:
they must be established from genuine mixed differentiation of
`normalizedKernel`. Consequently the theorem below is a conditional
bridge, not a proof of W2 < 0 or the full Nuttall conjecture.
-/

namespace W5

/-- The first-order Taylor slope of the positive coordinate gauge. -/
noncomputable def firstGaugeSlope (x : ℝ) : ℝ :=
  1 / x - (5 * x) / 4

/-- The first-order Taylor slope of the logarithmic coordinate shift. -/
noncomputable def firstShiftSlope (x : ℝ) : ℝ :=
  x / 4

/-- Actual normalized matrix assembled from analytic mixed derivatives,
rather than from the numerical surrogate `thetaCoefficient`. -/
noncomputable def normalizedMatrixTwo (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (fun i j =>
    analyticCoeff x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)

/-- The three exact first-order mixed-jet identities still requiring
analytic differentiation. The (0,0) identity is already unconditional.
The fourth entry features the actual derivative of the theta series. -/
def OrderTwoNormalizedJetData (x : ℝ) : Prop :=
  let c := kernelNormalization x
  let a := firstGaugeSlope x
  let b := firstShiftSlope x
  let t := thetaTimeOfX x
  analyticCoeff x (0 : Fin 5) (1 : Fin 5) =
    c * (a * Psi1 t - b * Phi t) ∧
  analyticCoeff x (1 : Fin 5) (0 : Fin 5) =
    c * (a * Psi1 t - b * Phi t) ∧
  analyticCoeff x (1 : Fin 5) (1 : Fin 5) =
    c * (a ^ 2 * Psi1 t - 2 * a * b * Phi t -
      b ^ 2 * (∑' n : ℕ, phiSummandDerivative n t))

/-- The zeroth entry uses no differentiation interchange or sign oracle. -/
theorem analyticCoeff_zero_zero_exact (x : ℝ) :
    analyticCoeff x (0 : Fin 5) (0 : Fin 5) =
      kernelNormalization x * Psi1 (thetaTimeOfX x) := by
  rw [analyticCoeff_zero_zero, normalizedKernel_zero_zero]

/-- The precise factor relating a normalized 2-by-2 determinant
to the original W2, once the three mixed-jet identities are proved.
The factor is `c² (x/4)²`, as predicted by the analytic
Taylor-coordinate transformation. -/
theorem normalizedMatrixTwo_det_of_jet
    (x : ℝ) (h : OrderTwoNormalizedJetData x) :
    (normalizedMatrixTwo x).det =
      (kernelNormalization x) ^ 2 * (firstShiftSlope x) ^ 2 *
        W 2 (thetaTimeOfX x) := by
  dsimp [OrderTwoNormalizedJetData] at h
  rcases h with ⟨h01, h10, h11⟩
  rw [Matrix.det_fin_two]
  change
    analyticCoeff x (0 : Fin 5) (0 : Fin 5) *
        analyticCoeff x (1 : Fin 5) (1 : Fin 5) -
      analyticCoeff x (0 : Fin 5) (1 : Fin 5) *
        analyticCoeff x (1 : Fin 5) (0 : Fin 5) =
      kernelNormalization x ^ 2 * firstShiftSlope x ^ 2 *
        W 2 (thetaTimeOfX x)
  rw [analyticCoeff_zero_zero_exact x, h01, h10, h11]
  rw [W_two_eq_original_theta_derivatives]
  ring

/-- For t >= 0, the order-two determinant sign is *equivalent* to the
original W2 sign, conditional solely on the three explicit
mixed-derivative identities above. -/
theorem normalizedMatrixTwo_negative_iff_W_two_negative
    (t : ℝ) (ht : 0 ≤ t)
    (h : OrderTwoNormalizedJetData (xOfT t)) :
    (normalizedMatrixTwo (xOfT t)).det < 0 ↔ W 2 t < 0 := by
  have hx : 0 < xOfT t := (xOfT_positive_and_bounded t ht).1
  have hc : 0 < kernelNormalization (xOfT t) :=
    kernelNormalization_pos (xOfT t) hx
  have hb : 0 < firstShiftSlope (xOfT t) := by
    dsimp [firstShiftSlope]
    positivity
  have hfactor :
      0 < kernelNormalization (xOfT t) ^ 2 *
        firstShiftSlope (xOfT t) ^ 2 :=
    mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hb)
  rw [normalizedMatrixTwo_det_of_jet (xOfT t) h,
    thetaTimeOfX_xOfT]
  constructor
  · intro hneg
    by_contra hn
    have hw : 0 ≤ W 2 t := le_of_not_gt hn
    have hnonneg : 0 ≤
        (kernelNormalization (xOfT t) ^ 2 *
          firstShiftSlope (xOfT t) ^ 2) * W 2 t :=
      mul_nonneg hfactor.le hw
    linarith
  · intro hw
    exact mul_neg_of_pos_of_neg hfactor hw

end W5
