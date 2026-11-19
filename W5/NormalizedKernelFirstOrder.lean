import W5.NormalizedKernelSymmetry

/-!
# Genuine first mixed Taylor derivatives of the normalized theta kernel

This proof differentiates the original `Psi1` integral through the
previously established fundamental theorem of calculus and uses only
ordinary one-dimensional chain and product rules. It does not identify
the normalized coefficient with the numerical certificate's
`thetaCoefficient`, and it does not establish the W2 sign.
-/

namespace W5

/-- The zero-left section of the *original* normalized kernel. -/
theorem normalizedKernel_zero_left (x v : ℝ) :
    normalizedKernel x 0 v =
      kernelNormalization x *
        (Real.exp (v / x) / (1 + x * v) ^ ((5:ℝ)/4)) *
        Psi1 (thetaTimeOfX x + Real.log (1 + x * v) / 4) := by
  simp [normalizedKernel, kernelNormalization, thetaTimeOfX]

/-- Differentiation of the affine logarithmic argument at the origin. -/
private theorem normalizedKernel_log_hasDerivAt (x : ℝ) :
    HasDerivAt (fun v : ℝ => Real.log (1 + x * v)) x 0 := by
  have hbase : HasDerivAt (fun v : ℝ => 1 + x * v) x 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_mul x).const_add 1 using 1
    · funext v
      ring
    · ring
  have hlog : HasDerivAt Real.log 1 (1:ℝ) := by
    simpa using (Real.hasDerivAt_log (by norm_num : (1:ℝ) ≠ 0))
  have houter := Real.hasDerivAt_log
    (show (1:ℝ) + x*(0:ℝ) ≠ 0 by simp)
  convert houter.comp (0:ℝ) hbase using 1 <;> simp

/-- The logarithmic shift has derivative exactly x/4 at zero. -/
private theorem normalizedKernel_shift_hasDerivAt (x : ℝ) :
    HasDerivAt
      (fun v : ℝ => thetaTimeOfX x + Real.log (1 + x * v) / 4)
      (firstShiftSlope x) 0 := by
  have h := ((normalizedKernel_log_hasDerivAt x).const_mul ((1:ℝ)/4)).const_add
    (thetaTimeOfX x)
  convert h using 1
  · funext v
    ring
  · dsimp [firstShiftSlope]
    ring

/-- Derivative of the normalized exponential gauge at the origin. -/
private theorem normalizedKernel_gauge_hasDerivAt (x : ℝ) :
    HasDerivAt
      (fun v : ℝ => Real.exp (v/x) / (1 + x*v)^((5:ℝ)/4))
      (firstGaugeSlope x) 0 := by
  have harg : HasDerivAt (fun v : ℝ => v / x) (1/x) 0 := by
    convert (hasDerivAt_id (0:ℝ)).const_mul (1/x) using 1
    · funext v
      ring
    · ring
  have he : HasDerivAt (fun v : ℝ => Real.exp (v/x)) (1/x) 0 := by
    convert (Real.hasDerivAt_exp ((0:ℝ)/x)).comp (0:ℝ) harg using 1 <;> simp
  have hbase : HasDerivAt (fun v : ℝ => 1 + x * v) x 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_mul x).const_add 1 using 1
    · funext v
      ring
    · ring
  have hp : HasDerivAt
      (fun v : ℝ => (1 + x*v)^((5:ℝ)/4)) (((5:ℝ)/4)*x) 0 := by
    have hh := (Real.hasDerivAt_rpow_const
      (Or.inl (show (1:ℝ) + x*(0:ℝ) ≠ 0 by simp)) ((5:ℝ)/4)).comp (0:ℝ) hbase
    convert hh using 1 <;> norm_num
  have h := he.div hp (by norm_num : (1 + x * (0:ℝ))^((5:ℝ)/4) ≠ 0)
  convert h using 1
  · funext v
    rfl
  · simp [firstGaugeSlope] <;> ring

/-- Strictly analytic origin: no unproved derivative/interchange premise.
This uses the already proved derivative of the genuine improper theta
integral, namely `Psi1' = -Phi`. -/
theorem normalizedKernel_zero_left_hasDerivAt (x : ℝ) :
    HasDerivAt (fun v : ℝ => normalizedKernel x 0 v)
      (kernelNormalization x *
        (firstGaugeSlope x * Psi1 (thetaTimeOfX x) -
          firstShiftSlope x * Phi (thetaTimeOfX x))) 0 := by
  have hg := normalizedKernel_gauge_hasDerivAt x
  have hs := normalizedKernel_shift_hasDerivAt x
  have hpsi : HasDerivAt
      (fun v : ℝ => Psi1 (thetaTimeOfX x + Real.log (1 + x*v)/4))
      (-Phi (thetaTimeOfX x) * firstShiftSlope x) 0 := by
    convert (Psi1_hasDerivAt (thetaTimeOfX x + Real.log (1 + x*(0:ℝ))/4)).comp (0:ℝ) hs using 1 <;> simp
  have h := (hg.mul hpsi).const_mul (kernelNormalization x)
  convert h using 1
  · funext v
    rw [normalizedKernel_zero_left]
    ring
  · simp <;> ring

/-- The first nonconstant mixed analytic Taylor coefficient,
unconditionally for every real x. -/
theorem analyticCoeff_zero_one_exact (x : ℝ) :
    analyticCoeff x (0:Fin 5) (1:Fin 5) =
      kernelNormalization x *
        (firstGaugeSlope x * Psi1 (thetaTimeOfX x) -
          firstShiftSlope x * Phi (thetaTimeOfX x)) := by
  rw [analyticCoeff_zero_one_deriv]
  exact (normalizedKernel_zero_left_hasDerivAt x).deriv

/-- Its mirror is equal by proved symmetry, not by an additional
assumption on mixed derivatives. -/
theorem analyticCoeff_one_zero_exact (x : ℝ) :
    analyticCoeff x (1:Fin 5) (0:Fin 5) =
      kernelNormalization x *
        (firstGaugeSlope x * Psi1 (thetaTimeOfX x) -
          firstShiftSlope x * Phi (thetaTimeOfX x)) := by
  rw [← analyticCoeff_zero_one_eq_one_zero]
  exact analyticCoeff_zero_one_exact x

end W5
