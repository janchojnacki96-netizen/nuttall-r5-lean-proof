import W5.ThetaActualNormalizedGammaSquareSeries

/-!
# Exact Gaussian integrand under the original incomplete-gamma substitution

In the genuine normalized Nuttall kernel, a square-index gamma integral
contains the exponent -p*y*z, with
  y = x^(-2) (1+x*u)(1+x*v).
For p=n²>0 the proposed substitution is
  z = 1+w*x²/p.

The exponent must be rewritten using the ORIGINAL, unshifted x^(-2)
normalization; the prior verified five-parameter exponent identity
does that exactly, including the constant exp(-w).

We prove the pointwise equality of the true gamma integrand
with the existing numerical certificate's weighted Gaussian integrand.
This uses only the already verified algebraic exponential identity and
ordered-field cancellation, no new Taylor coefficient calculations.

The measure-level change of variables from z>1 to w>0
(and its Jacobian x²/p) remains separate.
-/

namespace W5

/-- The exact affine substitution argument for a nonzero square index.
Its exponent coefficient is p+w*x², matching the certificate. -/
theorem theta_gamma_affine_coefficient
    (x p w : ℝ) (hp : p ≠ 0) :
    p * (1 + w*x^2/p) = p + w*x^2 := by
  field_simp [hp]
  ring

/-- For p>0 and w≥0, the transformed gamma coordinate is in [1,∞).
This ensures the real fourth root has its intended positive branch. -/
theorem theta_gamma_affine_ge_one
    (x p w : ℝ) (hp : 0 < p) (hw : 0 ≤ w) :
    1 ≤ 1 + w*x^2/p := by
  have hnonneg : 0 ≤ w*x^2/p := by positivity
  linarith

/-- The actual original theta gamma integrand, after the affine
substitution z = 1+w*x²/p, is the EXACT weighted Gaussian
model from the certificate, with the same exp(-w) factor.
No assumption on the signs of u or v is needed. -/
theorem theta_gamma_affine_weighted_gaussian_exact
    (x p u v w : ℝ) (hx : x ≠ 0) (hp : p ≠ 0) :
    (Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)) *
      ((1+w*x^2/p)^((1:ℝ)/4) *
        Real.exp (-p*thetaShiftedYAlgebraic x u v *
          (1+w*x^2/p))) =
    Real.exp (-(p-1)/x^2) *
      (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        thetaGaussianModel
          ((p-1)/x+w*x) (p+w*x^2) u v) := by
  let y : ℝ := thetaShiftedYAlgebraic x u v
  let E : ℝ :=
    Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)
  have hprod := theta_gamma_affine_coefficient x p w hp
  have harg :
      -p*y*(1+w*x^2/p) = -(p+w*x^2)*y := by
    rw [← hprod]
    ring
  have hexp :
      E * Real.exp (-(p+w*x^2)*y) =
        Real.exp (-(p-1)/x^2) * Real.exp (-w) *
          thetaGaussianModel
            ((p-1)/x+w*x) (p+w*x^2) u v := by
    simpa only [E, y, thetaGaussianModel] using
      (thetaNormalizedGaussianExp_eq_certificateGaussianExp
        x p u v w hx)
  change E * ((1+w*x^2/p)^((1:ℝ)/4) *
    Real.exp (-p*y*(1+w*x^2/p))) =
      Real.exp (-(p-1)/x^2) *
        (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          thetaGaussianModel ((p-1)/x+w*x) (p+w*x^2) u v)
  calc
    E * ((1+w*x^2/p)^((1:ℝ)/4) *
      Real.exp (-p*y*(1+w*x^2/p))) =
        (E * Real.exp (-(p+w*x^2)*y)) *
          (1+w*x^2/p)^((1:ℝ)/4) := by
          rw [harg]
          ring
    _ = (Real.exp (-(p-1)/x^2) * Real.exp (-w) *
          thetaGaussianModel ((p-1)/x+w*x) (p+w*x^2) u v) *
            (1+w*x^2/p)^((1:ℝ)/4) := by rw [hexp]
    _ = _ := by ring

end W5
