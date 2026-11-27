import Mathlib.Analysis.Polynomial.Fourier

namespace Nuttall

open Complex MeasureTheory AddCircle
open scoped Real Polynomial

local instance : Fact (0 < 2 * π) := Fact.mk Real.two_pi_pos

/-- Cauchy's coefficient bound written as the mean of the modulus on the unit circle.
This uses the existing identification of polynomial and Fourier coefficients. -/
theorem norm_polynomialCoeff_le_circleAverage (p : ℂ[X]) (n : ℕ) :
    ‖p.coeff n‖ ≤ Real.circleAverage (fun z => ‖p.eval z‖) 0 1 := by
  calc
    ‖p.coeff n‖ = ‖∫ θ : AddCircle (2 * π), fourier (-(n : ℤ)) θ • p.toAddCircle θ
        ∂haarAddCircle‖ := by
      rw [← p.fourierCoeff_toAddCircle_natCast n]
      rfl
    _ ≤ ∫ θ : AddCircle (2 * π), ‖fourier (-(n : ℤ)) θ • p.toAddCircle θ‖
        ∂haarAddCircle := norm_integral_le_integral_norm _
    _ = ∫ θ : AddCircle (2 * π), ‖p.toAddCircle θ‖ ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards with θ
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    _ = _ := by
      rw [AddCircle.integral_haarAddCircle, Real.circleAverage,
        ← AddCircle.intervalIntegral_preimage (2 * π) 0]
      simp [Polynomial.toAddCircle, AddCircle.toCircle, circleMap]

#print axioms norm_polynomialCoeff_le_circleAverage

end Nuttall
