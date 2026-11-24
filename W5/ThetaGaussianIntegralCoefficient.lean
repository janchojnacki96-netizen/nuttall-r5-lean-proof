import W5.ThetaGaussianModelLowOrder
import W5.OrderTwoThetaIntegralForms

/-!
# The original theta (1,1) coefficient as an integral of genuine
Gaussian mixed derivatives

The polynomial `d² - q` in the independent numerical certificate
is precisely the mixed derivative of the elementary Gaussian
`exp (-d*(u+v)-q*u*v)` at the origin.

This theorem replaces every (1,1) coefficient polynomial in the
ORIGINAL theta infinite series and its improper integral by that
genuine Gaussian mixed derivative. It does not interchange a
derivative and an integral or infinite sum. Those interchanges, or
a direct analytical alternative, remain to be proved.
-/

namespace W5
open MeasureTheory

/-- Genuine (1,1) mixed derivative of the elementary Gaussian. -/
noncomputable def gaussianMixedCoeff11 (d q : ℝ) : ℝ :=
  deriv (fun u : ℝ =>
    deriv (fun v : ℝ => thetaGaussianModel d q u v) 0) 0

theorem gaussianMixedCoeff11_exact (d q : ℝ) :
    gaussianMixedCoeff11 d q = d ^ 2 - q := by
  exact thetaGaussianModel_mixed_deriv_zero d q

/-- The numerical theta coefficient has an EXACT representation
by mixed derivatives of the elementary Gaussian inside the integral.
No unproved differentiation-under-integral premise is used. -/
theorem thetaCoefficient_one_one_gaussian_derivatives (x : ℝ) :
    thetaCoefficient x (1 : Fin 5) (1 : Fin 5) =
      ∑' n : ℕ, if n = 0 then 0 else
        let p : ℝ := (n : ℝ)^2
        let d0 : ℝ := (p - 1) / x
        let integral : ℝ :=
          ∫ w in Set.Ici (0 : ℝ),
            Real.exp (-w) * (1 + w*x^2/p)^((1:ℝ)/4) *
              gaussianMixedCoeff11 (d0+w*x) (p+w*x^2)
              ∂MeasureTheory.volume
        p * Real.exp (-(p-1)/x^2) *
          (gaussianMixedCoeff11 d0 p - x^2/(4*p)*integral) := by
  rw [thetaCoefficient_one_one_integral]
  simp only [gaussianMixedCoeff11_exact]

end W5
