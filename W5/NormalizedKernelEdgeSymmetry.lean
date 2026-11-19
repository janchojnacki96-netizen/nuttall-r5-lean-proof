import W5.NormalizedKernelOrderThree

/-!
# Genuine edge symmetry for ALL normalized coefficient matrices up to 5

Because the original normalized theta kernel is symmetric in its
two real arguments, the Taylor coefficients with one index zero
agree with their transposes, at every order from zero through four.
This result uses only equality of functions and iterated derivatives:
no commutation-of-mixed-derivatives assumption is required.

For two *positive* indices, symmetry of mixed derivatives still
requires an independent smoothness argument, not supplied here.
-/

namespace W5

/-- Unconditional edge symmetry of the ORIGINAL analytic coefficients.
Valid for every real x and all derivative orders admitted by Fin 5. -/
theorem analyticCoeff_zero_eq_transpose (x : ℝ) (j : Fin 5) :
    analyticCoeff x (0 : Fin 5) j =
      analyticCoeff x j (0 : Fin 5) := by
  have hf : (fun v : ℝ => normalizedKernel x 0 v) =
      (fun v : ℝ => normalizedKernel x v 0) := by
    funext v
    exact normalizedKernel_swap x 0 v
  simp only [analyticCoeff, iteratedDeriv_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
  rw [hf]

/-- In particular the previously missing order-(0,2) coefficient
and its mirrored (2,0) coefficient are genuinely equal. -/
theorem analyticCoeff_zero_two_eq_two_zero (x : ℝ) :
    analyticCoeff x (0 : Fin 5) (2 : Fin 5) =
      analyticCoeff x (2 : Fin 5) (0 : Fin 5) :=
  analyticCoeff_zero_eq_transpose x 2

end W5
