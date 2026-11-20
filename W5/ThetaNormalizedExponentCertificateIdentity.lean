import W5.ThetaNormalizedKernelClosedSeriesBridge

/-!
# One exact two-variable Gaussian exponent identity for the ORIGINAL kernel

The genuine normalizedKernel of PR #93 contains the shifted
original theta y-coordinate
  y = (1/x²)*(1+x*u)*(1+x*v).

After the correction-integral substitution
  z = 1 + w*x²/p,
the exact exponent becomes
  1/x² + u/x + v/x - (p+w*x²)*y.

One elementary ring identity shows it equals
  -(p-1)/x² - w
  - ((p-1)/x + w*x)*(u+v)
  - (p+w*x²)*u*v.

This simultaneously identifies the genuine MAIN term (w=0)
and EVERY corrected Gaussian term with the existing numerical
certificate's two-variable d_w/q_w coefficients.

The proof is a single Mathlib ordered-field normalization,
not 25 individual Taylor-coefficient computations. It uses
no unproved analytic interchange and does not yet justify
the gamma-integral change of variables or derivative extraction.
-/

namespace W5

/-- The exact positive shifted y-coordinate of the normalized
Nuttall kernel, written in rational algebraic form. -/
noncomputable def thetaShiftedYAlgebraic
    (x u v : ℝ) : ℝ :=
  (1/x^2)*(1+x*u)*(1+x*v)

/-- Fundamental exponent identity with arbitrary real p and w.
This is the SAME algebraic identity for all 25 original
theta polynomial coefficients and all Gaussian square indices. -/
theorem thetaNormalizedExponent_eq_certificateExponent
    (x p u v w : ℝ) (hx : x ≠ 0) :
    1/x^2 + u/x + v/x -
        (p+w*x^2)*thetaShiftedYAlgebraic x u v =
      -(p-1)/x^2 - w -
        (((p-1)/x+w*x)*(u+v) + (p+w*x^2)*u*v) := by
  unfold thetaShiftedYAlgebraic
  field_simp [hx]
  ring

/-- The exact REAL EXPONENTIAL of the normalized kernel
equals the Gaussian factor used in the numerical theta
certificate. Crucially, no asymptotic expansion is involved. -/
theorem thetaNormalizedGaussianExp_eq_certificateGaussianExp
    (x p u v w : ℝ) (hx : x ≠ 0) :
    Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x) *
      Real.exp (-(p+w*x^2)*thetaShiftedYAlgebraic x u v) =
    Real.exp (-(p-1)/x^2) * Real.exp (-w) *
      Real.exp (-(((p-1)/x+w*x)*(u+v) +
        (p+w*x^2)*u*v)) := by
  simp only [← Real.exp_add]
  congr 1
  exact thetaNormalizedExponent_eq_certificateExponent
    x p u v w hx

/-- Specialize the universal identity to the actual original
elementary square-index Gaussian term (w=0). -/
theorem thetaOriginalMainGaussianExp_eq_certificateMain
    (x p u v : ℝ) (hx : x ≠ 0) :
    Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x) *
      Real.exp (-p*thetaShiftedYAlgebraic x u v) =
    Real.exp (-(p-1)/x^2) *
      Real.exp (-((p-1)/x*(u+v) + p*u*v)) := by
  have h := thetaNormalizedGaussianExp_eq_certificateGaussianExp
    x p u v 0 hx
  simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using h

/-- At the original symmetric Taylor origin both Gaussian
factors reduce to the SAME exact square-index damping.
No logarithm or Taylor remainder is needed. -/
theorem thetaOriginalMainGaussianExp_at_origin
    (x p : ℝ) (hx : x ≠ 0) :
    Real.exp (1/x^2) *
      Real.exp (-p*thetaShiftedYAlgebraic x 0 0) =
    Real.exp (-(p-1)/x^2) := by
  have h := thetaOriginalMainGaussianExp_eq_certificateMain
    x p 0 0 hx
  simpa [thetaShiftedYAlgebraic] using h

end W5
