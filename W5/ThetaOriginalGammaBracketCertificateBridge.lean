import W5.ThetaGammaMathlibAffineIntegralSubstitution

/-!
# An exact ORIGINAL single-square gamma bracket equals its certificate integral

The original normalizedKernel was proved in #109 to be the TRUE square
index gamma series, not an independent approximation. The complete
pointwise exponent identity is in #110. The exact half-line affine
integral substitution z = 1+(x²/p) w is proved from Mathlib in #111.

These existing results can now be composed: for each p>0, the
full original incomplete-gamma bracket, after multiplication by the
real normalization exponential, becomes precisely the certificate's
Gaussian main term minus its weighted w-integral correction.

No new Fubini/derivative interchange is used. This identity is the
substantial termwise analytic part of the missing
`thetaTransformCorrect`; extracting the 25 mixed Taylor derivatives
of the entire series is a subsequent task.
-/

namespace W5
open MeasureTheory

/-- The complete true gamma integral, multiplied by the Nuttall
exponential gauge, becomes the REAL certificate correction
integral including the exact Jacobian x²/p. -/
theorem theta_original_gamma_integral_eq_certificate_integral
    (x p u v : ℝ) (hx : 0 < x) (hp : 0 < p) :
    (Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)) *
      (∫ z in Set.Ioi (1:ℝ),
        z^((1:ℝ)/4) *
          Real.exp (-p*thetaShiftedYAlgebraic x u v*z)) =
    (x^2/p) * Real.exp (-(p-1)/x^2) *
      (∫ w in Set.Ioi (0:ℝ),
        Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          thetaGaussianModel ((p-1)/x+w*x) (p+w*x^2) u v) := by
  let y : ℝ := thetaShiftedYAlgebraic x u v
  let c : ℝ := x^2/p
  let E : ℝ := Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)
  let f : ℝ → ℝ := fun w =>
    (1+c*w)^((1:ℝ)/4) * Real.exp (-p*y*(1+c*w))
  let g : ℝ → ℝ := fun w =>
    Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
      thetaGaussianModel ((p-1)/x+w*x) (p+w*x^2) u v
  have hz (w : ℝ) : 1+c*w = 1+w*x^2/p := by
    dsimp [c]
    ring
  have hpoint (w : ℝ) :
      E * f w = Real.exp (-(p-1)/x^2) * g w := by
    change E * ((1+c*w)^((1:ℝ)/4) *
      Real.exp (-p*y*(1+c*w))) =
      Real.exp (-(p-1)/x^2) *
        (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          thetaGaussianModel ((p-1)/x+w*x) (p+w*x^2) u v)
    calc
      E * ((1+c*w)^((1:ℝ)/4) *
          Real.exp (-p*y*(1+c*w))) =
        E * ((1+w*x^2/p)^((1:ℝ)/4) *
          Real.exp (-p*y*(1+w*x^2/p))) := by rw [hz]
      _ = _ :=
        theta_gamma_affine_weighted_gaussian_exact
          x p u v w hx.ne' hp.ne'
  have hgamma :
      (∫ z in Set.Ioi (1:ℝ),
        z^((1:ℝ)/4) * Real.exp (-p*y*z)) =
        c * (∫ w in Set.Ioi (0:ℝ), f w) := by
    exact theta_gamma_integral_affine_exact x p y hx hp
  have hpointintegral :
      (∫ w in Set.Ioi (0:ℝ), E * f w) =
        (∫ w in Set.Ioi (0:ℝ),
          Real.exp (-(p-1)/x^2) * g w) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w _
    exact hpoint w
  change
    E * (∫ z in Set.Ioi (1:ℝ),
      z^((1:ℝ)/4) * Real.exp (-p*y*z)) =
      c * Real.exp (-(p-1)/x^2) *
        (∫ w in Set.Ioi (0:ℝ), g w)
  calc
    E * (∫ z in Set.Ioi (1:ℝ),
        z^((1:ℝ)/4) * Real.exp (-p*y*z)) =
        E * (c * (∫ w in Set.Ioi (0:ℝ), f w)) := by rw [hgamma]
    _ = c * (E * (∫ w in Set.Ioi (0:ℝ), f w)) := by ring
    _ = c * (∫ w in Set.Ioi (0:ℝ), E * f w) := by
          rw [integral_const_mul]
    _ = c * (∫ w in Set.Ioi (0:ℝ),
        Real.exp (-(p-1)/x^2) * g w) := by rw [hpointintegral]
    _ = c * (Real.exp (-(p-1)/x^2) *
        (∫ w in Set.Ioi (0:ℝ), g w)) := by rw [integral_const_mul]
    _ = _ := by ring

/-- The full gamma bracket of the ORIGINAL normalized kernel is
exactly the main Gaussian model minus x²/(4p) times the actual
certificate w-integral. This is not a surrogate coefficient
identity: it holds pointwise for all u,v and positive x,p. -/
theorem theta_original_gamma_bracket_eq_certificate
    (x p u v : ℝ) (hx : 0 < x) (hp : 0 < p) :
    (Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)) *
      thetaOriginalGammaBracket p (thetaShiftedYAlgebraic x u v) =
      Real.exp (-(p-1)/x^2) *
        (thetaGaussianModel ((p-1)/x) p u v -
          (x^2/(4*p)) *
            (∫ w in Set.Ioi (0:ℝ),
              Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                thetaGaussianModel ((p-1)/x+w*x)
                  (p+w*x^2) u v)) := by
  let y : ℝ := thetaShiftedYAlgebraic x u v
  let E : ℝ := Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x)
  let G : ℝ :=
    ∫ w in Set.Ioi (0:ℝ),
      Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        thetaGaussianModel ((p-1)/x+w*x) (p+w*x^2) u v
  have hbase :
      E * Real.exp (-p*y) =
        Real.exp (-(p-1)/x^2) *
          thetaGaussianModel ((p-1)/x) p u v :=
    thetaOriginalGaussian_eq_certificate_model x p u v hx.ne'
  have hcorr :
      E * (∫ z in Set.Ioi (1:ℝ),
        z^((1:ℝ)/4) * Real.exp (-p*y*z)) =
        (x^2/p) * Real.exp (-(p-1)/x^2) * G :=
    theta_original_gamma_integral_eq_certificate_integral
      x p u v hx hp
  have hcoef : (1/4:ℝ) * (x^2/p) = x^2/(4*p) := by
    field_simp [hp.ne']
    ring
  change E * thetaOriginalGammaBracket p y =
    Real.exp (-(p-1)/x^2) *
      (thetaGaussianModel ((p-1)/x) p u v -
        (x^2/(4*p))*G)
  calc
    E * thetaOriginalGammaBracket p y =
        E * Real.exp (-p*y) -
          (1/4:ℝ) * (E * (∫ z in Set.Ioi (1:ℝ),
            z^((1:ℝ)/4) * Real.exp (-p*y*z))) := by
          unfold thetaOriginalGammaBracket
          ring
    _ = Real.exp (-(p-1)/x^2) *
          thetaGaussianModel ((p-1)/x) p u v -
        (1/4:ℝ) * ((x^2/p) *
          Real.exp (-(p-1)/x^2) * G) := by rw [hbase, hcorr]
    _ = Real.exp (-(p-1)/x^2) *
          (thetaGaussianModel ((p-1)/x) p u v -
            (x^2/(4*p))*G) := by
          rw [← hcoef]
          ring

end W5
