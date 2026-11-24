import W5.NormalizedKernelOrderTwo

/-!
# Exact symmetry of the original normalized theta kernel

The two first-order off-diagonal normalized Taylor coefficients
coincide as a consequence of the defining two-variable symmetry.
No sign certificate, convergence interchange, or unproved regularity
hypothesis is used: the derivative functions are exactly equal.
This removes one redundant analytic obligation from the r=2 bridge.
-/

namespace W5

/-- The genuinely normalized theta kernel is symmetric in its two
Taylor variables, for every real x, u, v. -/
theorem normalizedKernel_swap (x u v : ℝ) :
    normalizedKernel x u v = normalizedKernel x v u := by
  unfold normalizedKernel
  simp only [add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc]

/-- The (0,1) Taylor coefficient is an actual ordinary derivative. -/
theorem analyticCoeff_zero_one_deriv (x : ℝ) :
    analyticCoeff x (0 : Fin 5) (1 : Fin 5) =
      deriv (fun v : ℝ => normalizedKernel x 0 v) 0 := by
  simp [analyticCoeff, iteratedDeriv_one]

/-- The (1,0) Taylor coefficient is the same derivative with the
two kernel variables exchanged. -/
theorem analyticCoeff_one_zero_deriv (x : ℝ) :
    analyticCoeff x (1 : Fin 5) (0 : Fin 5) =
      deriv (fun u : ℝ => normalizedKernel x u 0) 0 := by
  simp [analyticCoeff, iteratedDeriv_one]

/-- Equality of the genuine off-diagonal analytic Taylor coefficients:
the second order-one identity need not be separately verified. -/
theorem analyticCoeff_zero_one_eq_one_zero (x : ℝ) :
    analyticCoeff x (0 : Fin 5) (1 : Fin 5) =
      analyticCoeff x (1 : Fin 5) (0 : Fin 5) := by
  rw [analyticCoeff_zero_one_deriv, analyticCoeff_one_zero_deriv]
  have hf : (fun v : ℝ => normalizedKernel x 0 v) =
      (fun v : ℝ => normalizedKernel x v 0) := by
    funext v
    exact normalizedKernel_swap x 0 v
  exact congrArg (fun f : ℝ → ℝ => deriv f 0) hf

/-- Only TWO independent Taylor identities are needed for the full
r=2 normalization bridge. The third follows from symmetry. -/
def OrderTwoReducedJetData (x : ℝ) : Prop :=
  let c := kernelNormalization x
  let a := firstGaugeSlope x
  let b := firstShiftSlope x
  let t := thetaTimeOfX x
  analyticCoeff x (0 : Fin 5) (1 : Fin 5) =
    c * (a * Psi1 t - b * Phi t) ∧
  analyticCoeff x (1 : Fin 5) (1 : Fin 5) =
    c * (a ^ 2 * Psi1 t - 2 * a * b * Phi t -
      b ^ 2 * (∑' n : ℕ, phiSummandDerivative n t))

theorem orderTwoJetData_iff_reduced (x : ℝ) :
    OrderTwoNormalizedJetData x ↔ OrderTwoReducedJetData x := by
  dsimp [OrderTwoNormalizedJetData, OrderTwoReducedJetData]
  constructor
  · rintro ⟨h01, _, h11⟩
    exact ⟨h01, h11⟩
  · rintro ⟨h01, h11⟩
    refine ⟨h01, ?_, h11⟩
    rw [← analyticCoeff_zero_one_eq_one_zero x]
    exact h01

/-- Determinant formula depending on just two *independent*
analytic Taylor identities (the second off-diagonal entry is proved). -/
theorem normalizedMatrixTwo_det_of_reduced_jet (x : ℝ)
    (h : OrderTwoReducedJetData x) :
    (normalizedMatrixTwo x).det =
      kernelNormalization x ^ 2 * firstShiftSlope x ^ 2 *
        W 2 (thetaTimeOfX x) :=
  normalizedMatrixTwo_det_of_jet x
    ((orderTwoJetData_iff_reduced x).mpr h)

end W5
