import W5.OrderTwoPolynomialCoefficients

/-!
# Exact integral formulas for the three independent theta coefficients

These are definitional/algebraic reductions of the *original*
thetaCoefficient, not approximations. Their point is to expose the
explicit integral kernels that must be identified with derivatives
of normalizedKernel.

The order-(1,1) kernel is especially important because negativity
of this SINGLE coefficient suffices for the original W2 sign after
its analytic identification.
-/

namespace W5
open MeasureTheory

theorem thetaCoefficient_zero_zero_integral (x : ℝ) :
    thetaCoefficient x (0 : Fin 5) (0 : Fin 5) =
      ∑' n : ℕ, if n = 0 then 0 else
        let p : ℝ := (n : ℝ)^2
        let d0 : ℝ := (p - 1) / x
        let integral : ℝ :=
          ∫ w in Set.Ici (0 : ℝ),
            Real.exp (-w) * (1 + w*x^2/p)^((1:ℝ)/4)
              ∂MeasureTheory.volume
        p * Real.exp (-(p-1)/x^2) *
          (1 - x^2/(4*p)*integral) := by
  simp only [thetaCoefficient, coefficientPolynomial_zero_zero, mul_one]

theorem thetaCoefficient_zero_one_integral (x : ℝ) :
    thetaCoefficient x (0 : Fin 5) (1 : Fin 5) =
      ∑' n : ℕ, if n = 0 then 0 else
        let p : ℝ := (n : ℝ)^2
        let d0 : ℝ := (p - 1) / x
        let integral : ℝ :=
          ∫ w in Set.Ici (0 : ℝ),
            Real.exp (-w) * (1 + w*x^2/p)^((1:ℝ)/4) *
              (-(d0 + w*x)) ∂MeasureTheory.volume
        p * Real.exp (-(p-1)/x^2) *
          (-d0 - x^2/(4*p)*integral) := by
  simp only [thetaCoefficient, coefficientPolynomial_zero_one]

theorem thetaCoefficient_one_one_integral (x : ℝ) :
    thetaCoefficient x (1 : Fin 5) (1 : Fin 5) =
      ∑' n : ℕ, if n = 0 then 0 else
        let p : ℝ := (n : ℝ)^2
        let d0 : ℝ := (p - 1) / x
        let integral : ℝ :=
          ∫ w in Set.Ici (0 : ℝ),
            Real.exp (-w) * (1 + w*x^2/p)^((1:ℝ)/4) *
              ((d0+w*x)^2 - (p+w*x^2)) ∂MeasureTheory.volume
        p * Real.exp (-(p-1)/x^2) *
          ((d0^2-p) - x^2/(4*p)*integral) := by
  simp only [thetaCoefficient, coefficientPolynomial_one_one]

end W5
