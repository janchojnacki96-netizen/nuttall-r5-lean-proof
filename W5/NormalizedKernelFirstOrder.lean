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
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul x).const_add (1:ℝ))
  have houter := Real.hasDerivAt_log
    (show (1:ℝ) + x * (0:ℝ) ≠ 0 by simp)
  have h := houter.comp (0:ℝ) hbase
  simpa only [Function.comp_def, mul_zero, add_zero, inv_one, one_mul] using h

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
    convert (hasDerivAt_id (0:ℝ)).const_mul (1/x) using 1 <;>
      simp only [id_eq] <;> ring
  have he : HasDerivAt (fun v : ℝ => Real.exp (v/x)) (1/x) 0 := by
    have h := (Real.hasDerivAt_exp ((0:ℝ)/x)).comp (0:ℝ) harg
    simpa only [Function.comp_def, zero_div, Real.exp_zero, one_mul] using h
  have hbase : HasDerivAt (fun v : ℝ => 1 + x * v) x 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul x).const_add (1:ℝ))
  have hp : HasDerivAt
      (fun v : ℝ => (1 + x*v)^((5:ℝ)/4)) (((5:ℝ)/4)*x) 0 := by
    have houter : HasDerivAt
        (fun z : ℝ => z ^ ((5:ℝ)/4))
        (((5:ℝ)/4) * (1 + x*(0:ℝ)) ^ (((5:ℝ)/4) - 1))
        (1 + x*(0:ℝ)) := by
      exact Real.hasDerivAt_rpow_const
        (Or.inl (show (1:ℝ) + x*(0:ℝ) ≠ 0 by simp))
    have hh := houter.comp (0:ℝ) hbase
    simpa only [Function.comp_def, mul_zero, add_zero, one_rpow,
      mul_one] using hh
  have h := he.div hp (by norm_num : (1 + x * (0:ℝ))^((5:ℝ)/4) ≠ 0)
  convert h using 1
  all_goals
    first
    | funext v; rfl
    | simp [firstGaugeSlope] <;> ring

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
    have h := (Psi1_hasDerivAt
      (thetaTimeOfX x + Real.log (1 + x*(0:ℝ))/4)).comp (0:ℝ) hs
    simpa only [Function.comp_def, mul_zero, add_zero,
      Real.log_one, zero_div] using h
  have h := (hg.mul hpsi).const_mul (kernelNormalization x)
  convert h using 1 <;>
    simp [Pi.mul_apply, normalizedKernel_zero_left] <;> ring

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


/-- The only independent first-order-or-higher analytic entry
still missing for the original normalized two-by-two matrix. -/
def OrderTwoDiagonalJetData (x : ℝ) : Prop :=
  analyticCoeff x (1 : Fin 5) (1 : Fin 5) =
    kernelNormalization x *
      (firstGaugeSlope x ^ 2 * Psi1 (thetaTimeOfX x) -
        2 * firstGaugeSlope x * firstShiftSlope x * Phi (thetaTimeOfX x) -
        firstShiftSlope x ^ 2 *
          (∑' n : ℕ, phiSummandDerivative n (thetaTimeOfX x)))

/-- The normalized order-two determinant identity now needs only
ONE explicit analytic derivative equality. All lower-order
off-diagonal equalities are supplied by unconditional theorems above. -/
theorem normalizedMatrixTwo_det_of_diagonal_jet (x : ℝ)
    (h11 : OrderTwoDiagonalJetData x) :
    (normalizedMatrixTwo x).det =
      kernelNormalization x ^ 2 * firstShiftSlope x ^ 2 *
        W 2 (thetaTimeOfX x) := by
  apply normalizedMatrixTwo_det_of_jet x
  dsimp [OrderTwoNormalizedJetData, OrderTwoDiagonalJetData] at h11 ⊢
  exact ⟨analyticCoeff_zero_one_exact x,
    analyticCoeff_one_zero_exact x, h11⟩

/-- Along the original theta ray the remaining 2-by-2 sign test is
equivalent to the sign of the actual Wronskian, conditional only on
the genuine (1,1) analytic Taylor coefficient identity. -/
theorem normalizedMatrixTwo_negative_iff_W_two_negative_of_diagonal
    (t : ℝ) (ht : 0 ≤ t)
    (h11 : OrderTwoDiagonalJetData (xOfT t)) :
    (normalizedMatrixTwo (xOfT t)).det < 0 ↔ W 2 t < 0 := by
  have h : OrderTwoNormalizedJetData (xOfT t) := by
    dsimp [OrderTwoNormalizedJetData, OrderTwoDiagonalJetData] at h11 ⊢
    exact ⟨analyticCoeff_zero_one_exact (xOfT t),
      analyticCoeff_one_zero_exact (xOfT t), h11⟩
  exact normalizedMatrixTwo_negative_iff_W_two_negative t ht h



/-!
## The actual mixed derivative (1,1)

The following calculation does not use \`OrderTwoDiagonalJetData\`
as an assumption. It differentiates the genuine two-variable theta
kernel, relying on the previously established real derivatives of
\`Psi1\` and \`Phi\`.
-/

private noncomputable def thetaGauge (x u : ℝ) : ℝ :=
  Real.exp (u / x) / (1 + x * u) ^ ((5 : ℝ) / 4)

private noncomputable def thetaShift (x u : ℝ) : ℝ :=
  Real.log (1 + x * u) / 4

private theorem thetaGauge_zero (x : ℝ) : thetaGauge x 0 = 1 := by
  simp [thetaGauge]

private theorem thetaShift_zero (x : ℝ) : thetaShift x 0 = 0 := by
  simp [thetaShift]

/-- Exact factorization of the *genuine* normalized kernel, valid
without a positivity assumption on x or on the Taylor variables. -/
theorem normalizedKernel_factor (x u v : ℝ) :
    normalizedKernel x u v =
      kernelNormalization x * (thetaGauge x u * thetaGauge x v) *
        Psi1 (thetaTimeOfX x + thetaShift x u + thetaShift x v) := by
  simp only [normalizedKernel, kernelNormalization, thetaTimeOfX,
    thetaGauge, thetaShift]
  ring

/-- First derivative with respect to the second variable, at v=0,
but with the first variable still arbitrary. -/
theorem normalizedKernel_right_hasDerivAt_zero (x u : ℝ) :
    HasDerivAt (fun v : ℝ => normalizedKernel x u v)
      (kernelNormalization x * thetaGauge x u *
        (firstGaugeSlope x *
            Psi1 (thetaTimeOfX x + thetaShift x u) -
          firstShiftSlope x *
            Phi (thetaTimeOfX x + thetaShift x u))) 0 := by
  have hg : HasDerivAt (thetaGauge x) (firstGaugeSlope x) 0 := by
    change HasDerivAt
      (fun v : ℝ => Real.exp (v/x) / (1 + x*v)^((5:ℝ)/4))
      (firstGaugeSlope x) 0
    exact normalizedKernel_gauge_hasDerivAt x
  have hs : HasDerivAt
      (fun v : ℝ =>
        thetaTimeOfX x + thetaShift x u + thetaShift x v)
      (firstShiftSlope x) 0 := by
    have h := (normalizedKernel_shift_hasDerivAt x).const_add
      (thetaShift x u)
    convert h using 1 <;> dsimp [thetaShift] <;> ring
  have hp : HasDerivAt
      (fun v : ℝ =>
        Psi1 (thetaTimeOfX x + thetaShift x u + thetaShift x v))
      (-Phi (thetaTimeOfX x + thetaShift x u) *
        firstShiftSlope x) 0 := by
    have h := (Psi1_hasDerivAt
      (thetaTimeOfX x + thetaShift x u + thetaShift x 0)).comp (0 : ℝ) hs
    simpa only [Function.comp_def, thetaShift_zero, add_zero] using h
  have hprod := (hg.mul hp).const_mul
    (kernelNormalization x * thetaGauge x u)
  have hf :
      (fun v : ℝ => normalizedKernel x u v) =
        (fun v : ℝ =>
          (kernelNormalization x * thetaGauge x u) *
            (thetaGauge x v *
              Psi1 (thetaTimeOfX x + thetaShift x u + thetaShift x v))) := by
    funext v
    rw [normalizedKernel_factor]
    ring
  rw [hf]
  convert hprod using 1 <;>
    simp only [thetaGauge_zero, thetaShift_zero, add_zero] <;> ring

/-- Genuine mixed Taylor coefficient computed by differentiation of
the two-variable kernel. This is a derivative identity, NOT a
numerical determinant sign inequality. -/
theorem analyticCoeff_one_one_exact (x : ℝ) :
    analyticCoeff x (1 : Fin 5) (1 : Fin 5) =
      kernelNormalization x *
        (firstGaugeSlope x ^ 2 * Psi1 (thetaTimeOfX x) -
          2 * firstGaugeSlope x * firstShiftSlope x *
            Phi (thetaTimeOfX x) -
          firstShiftSlope x ^ 2 *
            (∑' n : ℕ, phiSummandDerivative n (thetaTimeOfX x))) := by
  let c : ℝ := kernelNormalization x
  let a : ℝ := firstGaugeSlope x
  let b : ℝ := firstShiftSlope x
  let t : ℝ := thetaTimeOfX x
  let G : ℝ → ℝ := thetaGauge x
  let S : ℝ → ℝ := fun u => t + thetaShift x u
  let Q : ℝ → ℝ := fun u => a * Psi1 (S u) - b * Phi (S u)
  have hs : HasDerivAt S b 0 := by
    simpa only [S, t, b, thetaShift] using normalizedKernel_shift_hasDerivAt x
  have hpsi : HasDerivAt (fun u : ℝ => Psi1 (S u))
      (-Phi t * b) 0 := by
    have h := (Psi1_hasDerivAt (S 0)).comp (0 : ℝ) hs
    simpa only [Function.comp_def, S, t, thetaShift,
      mul_zero, add_zero, Real.log_one, zero_div] using h
  have hphi : HasDerivAt (fun u : ℝ => Phi (S u))
      ((∑' n : ℕ, phiSummandDerivative n t) * b) 0 := by
    have h := (Phi_hasDerivAt (S 0)).comp (0 : ℝ) hs
    simpa only [Function.comp_def, S, t, thetaShift,
      mul_zero, add_zero, Real.log_one, zero_div] using h
  have hq : HasDerivAt Q
      (a * (-Phi t * b) -
        b * ((∑' n : ℕ, phiSummandDerivative n t) * b)) 0 := by
    exact (hpsi.const_mul a).sub (hphi.const_mul b)
  have hg : HasDerivAt G a 0 := by
    change HasDerivAt
      (fun v : ℝ => Real.exp (v/x) / (1 + x*v)^((5:ℝ)/4))
      (firstGaugeSlope x) 0
    exact normalizedKernel_gauge_hasDerivAt x
  have htotal := ((hg.mul hq).const_mul c)
  have hfun :
      (fun u : ℝ => deriv (fun v : ℝ => normalizedKernel x u v) 0) =
        (fun u : ℝ => c * (G u * Q u)) := by
    funext u
    have hv := (normalizedKernel_right_hasDerivAt_zero x u).deriv
    convert hv using 1 <;> dsimp [c, G, Q, S, a, b, t] <;> ring
  have hvalue :
      deriv (fun u : ℝ => c * (G u * Q u)) 0 =
        c * (a ^ 2 * Psi1 t -
          2 * a * b * Phi t -
          b ^ 2 * (∑' n : ℕ, phiSummandDerivative n t)) := by
    convert htotal.deriv using 1 <;>
      simp only [G, Q, S, thetaGauge_zero, thetaShift_zero,
        add_zero] <;> ring
  have hresult :
      deriv (fun u : ℝ =>
        deriv (fun v : ℝ => normalizedKernel x u v) 0) 0 =
        kernelNormalization x *
          (firstGaugeSlope x ^ 2 * Psi1 (thetaTimeOfX x) -
            2 * firstGaugeSlope x * firstShiftSlope x *
              Phi (thetaTimeOfX x) -
            firstShiftSlope x ^ 2 *
              (∑' n : ℕ, phiSummandDerivative n (thetaTimeOfX x))) := by
    rw [hfun, hvalue] <;> rfl
  simpa [analyticCoeff, iteratedDeriv_one] using hresult

/-- The remaining mixed-derivative premise for order two is actually
discharged, using only differentiability of the ORIGINAL theta kernel. -/
theorem orderTwoDiagonalJetData_proved (x : ℝ) :
    OrderTwoDiagonalJetData x := by
  exact analyticCoeff_one_one_exact x

/-- Exact, unconditional normalization factor for the ORIGINAL W2.
This does not assert that W2 has the desired negative sign. -/
theorem normalizedMatrixTwo_det_exact (x : ℝ) :
    (normalizedMatrixTwo x).det =
      kernelNormalization x ^ 2 * firstShiftSlope x ^ 2 *
        W 2 (thetaTimeOfX x) := by
  exact normalizedMatrixTwo_det_of_diagonal_jet x
    (orderTwoDiagonalJetData_proved x)

/-- Exact sign equivalence for the original W2 on its theta ray.
A separate certified or analytic inequality must prove negativity. -/
theorem normalizedMatrixTwo_negative_iff_W_two_negative_exact
    (t : ℝ) (ht : 0 ≤ t) :
    (normalizedMatrixTwo (xOfT t)).det < 0 ↔ W 2 t < 0 :=
  normalizedMatrixTwo_negative_iff_W_two_negative_of_diagonal
    t ht (orderTwoDiagonalJetData_proved (xOfT t))

end W5
