import W5.ThetaNormalizedExponentCertificateIdentity
import W5.ThetaGaussianModelLowOrder

/-!
# The genuine normalized Nuttall kernel as an exact square-index gamma series

The already checked closed-form identity for the ORIGINAL Psi1,
`normalizedKernel_eq_true_theta_closed_series`, contains scalar
normalization factors in front of a theta sum. A separate already
checked identity `theta_gauge_scalar_cancel` proves that the powers
y^(5/4) cancel those factors.

We move the constant through the *genuine* infinite sum using
Mathlib's `tsum_mul_left` (rather than postulating summability
or creating a second formal theta model). Every summand has an
elementary exponential factor and the ORIGINAL incomplete-gamma
integral; no derivative/integral interchange is performed.

We also connect the elementary Gaussian contribution directly to
the identical `thetaGaussianModel` used by the coefficient certificate.
The remaining step is the precise gamma-integral substitution
z = 1 + w*x²/p and then termwise mixed differentiation.
-/

namespace W5
open MeasureTheory

/-- The exact incomplete-gamma bracket from the original Psi1
closed form. No numerical approximation or simplification is made. -/
noncomputable def thetaOriginalGammaBracket (p y : ℝ) : ℝ :=
  Real.exp (-p*y) -
    (1/4 : ℝ) *
      (∫ z in Set.Ioi (1:ℝ),
        z^((1:ℝ)/4) * Real.exp (-p*y*z))

/-- The original normalized kernel equals the true theta
square-index gamma series on its verified local Taylor patch.
In particular the positive gauge factors disappear EXACTLY. -/
theorem normalizedKernel_eq_actual_gamma_square_series
    (x u v : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    normalizedKernel x u v =
      ∑' n : ℕ,
        (n:ℝ)^2 *
          (Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)) *
          thetaOriginalGammaBracket ((n:ℝ)^2)
            (thetaShiftedYAlgebraic x u v) := by
  let y : ℝ := thetaShiftedYAlgebraic x u v
  let C : ℝ :=
    (2 * Real.pi ^ ((1:ℝ)/4) * Real.exp (1/x^2) /
        (1/x^2)^((5:ℝ)/4)) *
      (Real.exp (u/x) * Real.exp (v/x) /
        ((1+x*u)^((5:ℝ)/4) * (1+x*v)^((5:ℝ)/4))) *
      (1/(4 * Real.pi ^ ((1:ℝ)/4)))
  let E : ℝ := Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)
  have hpu : 0 < 1+x*u :=
    theta_local_log_argument_pos x u hx hxB hu
  have hpv : 0 < 1+x*v :=
    theta_local_log_argument_pos x v hx hxB hv
  have hseries := normalizedKernel_eq_true_theta_closed_series
    x u v hx hxB hu hv
  rw [theta_shifted_y_exact x u v hx hpu hpv] at hseries
  change normalizedKernel x u v = C * thetaClosedYSeries y at hseries
  have hcancel : C * (2 * y^((5:ℝ)/4)) = E :=
    theta_gauge_scalar_cancel x u v hx hpu hpv
  calc
    normalizedKernel x u v = C * thetaClosedYSeries y := hseries
    _ = C * (∑' n : ℕ,
        2*(n:ℝ)^2*y^((5:ℝ)/4) *
          thetaOriginalGammaBracket ((n:ℝ)^2) y) := by
          rfl
    _ = ∑' n : ℕ,
          C * (2*(n:ℝ)^2*y^((5:ℝ)/4) *
            thetaOriginalGammaBracket ((n:ℝ)^2) y) := by
          rw [tsum_mul_left]
    _ = ∑' n : ℕ,
          (n:ℝ)^2 * E *
            thetaOriginalGammaBracket ((n:ℝ)^2) y := by
          apply tsum_congr
          intro n
          calc
            C * (2*(n:ℝ)^2*y^((5:ℝ)/4) *
                thetaOriginalGammaBracket ((n:ℝ)^2) y) =
              (C * (2*y^((5:ℝ)/4))) *
                ((n:ℝ)^2 *
                  thetaOriginalGammaBracket ((n:ℝ)^2) y) := by ring
            _ = E * ((n:ℝ)^2 *
                  thetaOriginalGammaBracket ((n:ℝ)^2) y) := by rw [hcancel]
            _ = (n:ℝ)^2 * E *
                  thetaOriginalGammaBracket ((n:ℝ)^2) y := by ring
    _ = ∑' n : ℕ,
          (n:ℝ)^2 *
            (Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)) *
            thetaOriginalGammaBracket ((n:ℝ)^2)
              (thetaShiftedYAlgebraic x u v) := by
          rfl

/-- The *elementary* original Gaussian summand (before the gamma
correction) equals the exact certificate Gaussian model, for any p.
This uses the previously verified all-parameter exponent identity,
not a formal Taylor expansion. -/
theorem thetaOriginalGaussian_eq_certificate_model
    (x p u v : ℝ) (hx : x ≠ 0) :
    Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x) *
      Real.exp (-p * thetaShiftedYAlgebraic x u v) =
      Real.exp (-(p-1)/x^2) *
        thetaGaussianModel ((p-1)/x) p u v := by
  have harg :
      -((p-1)/x*(u+v) + p*u*v) =
        -((p-1)/x)*(u+v) - p*u*v := by ring
  rw [thetaOriginalMainGaussianExp_eq_certificateMain x p u v hx]
  unfold thetaGaussianModel
  rw [harg]

end W5
