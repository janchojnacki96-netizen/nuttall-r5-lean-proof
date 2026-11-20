import W5.ThetaDensityClosedForm
import W5.ThetaInverseCoordinate
import W5.ThetaCoordinateIdentity

/-!
# Reuse the already proved ORIGINAL Psi1 closed form on a LOCAL shifted patch

Mathlib's real exponential substitution has ALREADY been used
in W5.ThetaExpSubstitution and W5.ThetaDensityClosedForm:
`Psi1_eq_thetaY_integral` is valid for ALL real t.

The original closed-form theorem was stated only for t>=0,
even though its proof uses just the weaker bound
  pi * exp(4*t) >= 1.

For the normalized two-Taylor-parameter kernel, one must
evaluate Psi1 at t + log(1+x*u)/4 + log(1+x*v)/4;
this may fall slightly below zero even at the edge t=0.
We reuse the full existing proof and prove its exact
positive-y hypothesis throughout the x/8 local box,
for 0<x<=145/256.

This closes a nontrivial DOMAIN gap needed by the future
`thetaTransformCorrect` proof, without repeating any
integration, incomplete gamma or infinite-series Fubini argument.

No analyticCoeff/thetaCoefficient identity or determinant
sign is asserted in this module.
-/

namespace W5
open MeasureTheory

/-- The already proved exact original Psi1 theta series formula
actually needs only the y-coordinate hypothesis y>=1,
not the stronger time-coordinate hypothesis t>=0. -/
theorem Psi1_eq_theta_closed_form_of_y_ge_one
    (t : ℝ)
    (hy : 1 ≤ Real.pi * Real.exp (4*t)) :
    Psi1 t =
      (1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) *
      (∑' n : ℕ,
        2 * (n:ℝ)^2 *
          (Real.pi * Real.exp (4*t)) ^ ((5:ℝ)/4) *
            (Real.exp (-(n:ℝ)^2 *
              (Real.pi * Real.exp (4*t))) -
             (1/4:ℝ) *
               (∫ v in Set.Ioi (1:ℝ),
                 v ^ ((1:ℝ)/4) *
                   Real.exp (-(n:ℝ)^2 *
                     (Real.pi * Real.exp (4*t))*v)))) := by
  have hclosed :
      (∫ y in Set.Ioi (Real.pi * Real.exp (4*t)),
          ∑' n : ℕ, thetaYIntegrand n y) =
      ∑' n : ℕ,
        2 * (n:ℝ)^2 *
          (Real.pi * Real.exp (4*t)) ^ ((5:ℝ)/4) *
            (Real.exp (-(n:ℝ)^2 *
              (Real.pi * Real.exp (4*t))) -
             (1/4:ℝ) *
               (∫ v in Set.Ioi (1:ℝ),
                 v ^ ((1:ℝ)/4) *
                   Real.exp (-(n:ℝ)^2 *
                     (Real.pi * Real.exp (4*t))*v))) := by
    simpa only [MeasureTheory.integral_Ici_eq_integral_Ioi] using
      (thetaY_integral_tsum_closed_form
        (Real.pi * Real.exp (4*t)) hy)
  rw [Psi1_eq_thetaY_integral, hclosed]

/-- The exact inverse theta time coordinate has y=1/x²
for x>0. This identity already follows from Mathlib's
Real.exp_log; no new substitution theorem is required. -/
theorem theta_y_of_thetaTimeOfX
    (x : ℝ) (hx : 0 < x) :
    Real.pi * Real.exp (4*thetaTimeOfX x) = 1/x^2 := by
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hpos : 0 < (1/x^2)/Real.pi := by
    positivity
  unfold thetaTimeOfX
  rw [show (4:ℝ)*(Real.log ((1/x^2)/Real.pi)/4) =
      Real.log ((1/x^2)/Real.pi) by ring, Real.exp_log hpos]
  field_simp [hp]
  <;> ring

/-- On the common original theta local x/8 box, the shifted
normalization argument is ALWAYS in the y>=1 region.
This is the exact domain condition required by the
already verified original Psi1 closed-form theorem. -/
theorem theta_shifted_y_ge_one_on_box
    (x u v : ℝ)
    (hx : 0 < x) (hxB : x ≤ (145:ℝ)/256)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    1 ≤ Real.pi * Real.exp
      (4*(thetaTimeOfX x +
        Real.log (1+x*u)/4 + Real.log (1+x*v)/4)) := by
  have hx2pos : 0 < x^2 := sq_pos_of_pos hx
  have hxsmall : x^2 ≤ (1:ℝ)/3 := by
    have hmul : 0 ≤ x*((145:ℝ)/256 - x) :=
      mul_nonneg hx.le (sub_nonneg.mpr hxB)
    nlinarith [hmul]
  have hua : -(1:ℝ)/24 ≤ x*u := by
    have hlow : -x/8 ≤ u := (abs_le.mp hu).1
    have hmul : 0 ≤ x*(u+x/8) :=
      mul_nonneg hx.le (by linarith)
    nlinarith [hmul, hxsmall]
  have hva : -(1:ℝ)/24 ≤ x*v := by
    have hlow : -x/8 ≤ v := (abs_le.mp hv).1
    have hmul : 0 ≤ x*(v+x/8) :=
      mul_nonneg hx.le (by linarith)
    nlinarith [hmul, hxsmall]
  have hpu : (23:ℝ)/24 ≤ 1+x*u := by linarith
  have hpv : (23:ℝ)/24 ≤ 1+x*v := by linarith
  have hu0 : 0 < 1+x*u := by linarith
  have hv0 : 0 < 1+x*v := by linarith
  have hprod :
      ((23:ℝ)/24)*((23:ℝ)/24) ≤ (1+x*u)*(1+x*v) :=
    mul_le_mul hpu hpv (by norm_num) (by linarith)
  have hxy : x^2 ≤ (1+x*u)*(1+x*v) := by
    linarith [hprod, hxsmall]
  have hratio :
      1 ≤ ((1+x*u)*(1+x*v))/x^2 :=
    (le_div_iff₀ hx2pos).mpr (by simpa using hxy)
  have hbase := theta_y_of_thetaTimeOfX x hx
  have hcoord := theta_coordinate_exp_identity
    x (thetaTimeOfX x) u v hu0 hv0
  rw [hbase] at hcoord
  calc
    1 ≤ ((1+x*u)*(1+x*v))/x^2 := hratio
    _ = (1/x^2)*(1+x*u)*(1+x*v) := by ring
    _ = Real.pi * Real.exp
        (4*(thetaTimeOfX x +
          Real.log (1+x*u)/4 + Real.log (1+x*v)/4)) := hcoord.symm

end W5
