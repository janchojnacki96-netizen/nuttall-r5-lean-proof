import W5.NormalizedKernelOrderThree

/-!
# A genuine second derivative for the logarithmic theta coordinate

At order three the triangular coordinate matrix involves the
quadratic Taylor coefficient of log(1+x*u)/4. Here it is obtained
from the actual real derivative (not assumed as a jet datum).
-/

namespace W5

/-- The logarithmic coordinate change occurring in the original kernel. -/
noncomputable def normalizedLogShift (x u : ℝ) : ℝ :=
  Real.log (1 + x * u) / 4

/-- Pointwise derivative at every point with nonzero logarithm argument. -/
theorem normalizedLogShift_hasDerivAt (x u : ℝ)
    (hu : 1 + x * u ≠ 0) :
    HasDerivAt (normalizedLogShift x) (x / (4 * (1 + x * u))) u := by
  have hbase : HasDerivAt (fun v : ℝ => 1 + x * v) x u := by
    simpa using (((hasDerivAt_id u).const_mul x).const_add (1 : ℝ))
  have hlog := (Real.hasDerivAt_log hu).comp u hbase
  have h := hlog.const_mul ((1 : ℝ) / 4)
  convert h using 1
  · funext v
    simp only [normalizedLogShift, Function.comp_def]
    ring
  · field_simp [hu] <;> ring

/-- A genuine second derivative of the coordinate shift at the
origin, equivalent to its quadratic coefficient -x²/8. -/
theorem normalizedLogShift_second_derivative (x : ℝ) :
    iteratedDeriv 2 (normalizedLogShift x) 0 =
      2 * secondShiftCoeff x := by
  have hden : HasDerivAt
      (fun u : ℝ => 4 * (1 + x * u)) (4 * x) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul x).const_add
      (1 : ℝ)).const_mul (4 : ℝ)
    convert h using 1
    · funext v
      simp only [id_eq]
      ring
    · ring
  have hq : HasDerivAt
      (fun u : ℝ => x / (4 * (1 + x * u)))
      (-x ^ 2 / 4) 0 := by
    have hconst : HasDerivAt (fun _ : ℝ => x) 0 0 :=
      hasDerivAt_const 0 x
    have h := hconst.div hden
      (by norm_num : 4 * (1 + x * (0 : ℝ)) ≠ 0)
    convert h using 1
    · simp only [mul_zero, add_zero, mul_one, zero_mul, sub_zero]
      norm_num
      ring
  have hne : ∀ᶠ u : ℝ in Filter.nhds (0 : ℝ), 1 + x * u ≠ 0 := by
    have hc : ContinuousAt (fun u : ℝ => 1 + x * u) 0 := by
      fun_prop
    exact hc.eventually_ne (by norm_num)
  have heq :
      (fun u : ℝ => deriv (normalizedLogShift x) u) =ᶠ[Filter.nhds (0 : ℝ)]
      (fun u : ℝ => x / (4 * (1 + x * u))) := by
    filter_upwards [hne] with u hu
    exact (normalizedLogShift_hasDerivAt x u hu).deriv
  have hsecond : HasDerivAt (deriv (normalizedLogShift x))
      (-x ^ 2 / 4) 0 :=
    hq.congr_of_eventuallyEq heq.symm
  rw [show (2 : ℕ) = 1 + 1 by omega,
    iteratedDeriv_succ, iteratedDeriv_one, hsecond.deriv]
  dsimp [secondShiftCoeff]
  ring

end W5
