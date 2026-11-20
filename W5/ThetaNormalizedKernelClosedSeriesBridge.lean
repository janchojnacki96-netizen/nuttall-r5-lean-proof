import W5.ThetaPsiClosedFormLocalShift
import W5.AnalyticTargets

/-!
# The original normalized Nuttall kernel is an exact, shifted theta series

This starts the ACTUAL kernel identity needed for thetaTransformCorrect,
using the already proved original-Psi1 gamma series rather than
reconstructing the change of variables or Fubini interchange.

For 0<x≤145/256 and |u|,|v|≤x/8 we establish:
* both logarithm arguments 1+x*u and 1+x*v are strictly positive;
* the genuine shifted theta y-coordinate is exactly
  ((1+x*u)*(1+x*v))/x²;
* all scalar y^(5/4) and (1+x*u)^(5/4) gauge factors CANCEL;
* the full original normalizedKernel equals an explicit series
  built from the true incomplete-gamma integrals.

The last two facts are pure algebra plus application of the
already verified Psi1 closed form. This file does NOT assert
interchange of 25 mixed derivatives with a nonuniform series,
nor does it assert coefficient/determinant signs.
-/

namespace W5
open MeasureTheory

/-- The local two-variable Taylor patch stays inside the
domain where the logarithm and real powers are positive. -/
theorem theta_local_log_argument_pos
    (x z : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256)
    (hz : |z| ≤ x/8) :
    0 < 1 + x*z := by
  have hx1 : x ≤ 1 := by linarith
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hl : -(x/8) ≤ z := (abs_le.mp hz).1
  have hm : 0 ≤ x*(z+x/8) :=
    mul_nonneg hx.le (by linarith)
  nlinarith [hm, hx2]

/-- The actual shifted original t-coordinate has this
exact y-coordinate, with no formal Taylor approximation. -/
theorem theta_shifted_y_exact
    (x u v : ℝ) (hx : 0 < x)
    (hu : 0 < 1+x*u) (hv : 0 < 1+x*v) :
    Real.pi * Real.exp
      (4*(thetaTimeOfX x +
        Real.log (1+x*u)/4 + Real.log (1+x*v)/4)) =
      (1/x^2)*(1+x*u)*(1+x*v) := by
  calc
    _ = (Real.pi * Real.exp (4*thetaTimeOfX x)) *
          (1+x*u)*(1+x*v) :=
      theta_coordinate_exp_identity x (thetaTimeOfX x) u v hu hv
    _ = (1/x^2)*(1+x*u)*(1+x*v) := by
      rw [theta_y_of_thetaTimeOfX x hx]

/-- Scalar normalization cancellation, already implicit in
the original Nuttall transform: y^(5/4) exactly cancels
the two real-power gauge factors, including the pi constants.

The positive y-domain hypotheses ensure Real.mul_rpow is
legitimate; no formal power-series reasoning is required. -/
theorem theta_gauge_scalar_cancel
    (x u v : ℝ) (hx : 0 < x)
    (hu : 0 < 1+x*u) (hv : 0 < 1+x*v) :
    (2 * Real.pi ^ ((1:ℝ)/4) * Real.exp (1/x^2) /
      (1/x^2) ^ ((5:ℝ)/4)) *
      (Real.exp (u/x) * Real.exp (v/x) /
        ((1+x*u)^((5:ℝ)/4) * (1+x*v)^((5:ℝ)/4))) *
      (1/(4 * Real.pi ^ ((1:ℝ)/4))) *
      (2 * ((1/x^2)*(1+x*u)*(1+x*v))^((5:ℝ)/4)) =
      Real.exp (1/x^2) * Real.exp (u/x) * Real.exp (v/x) := by
  have hy : 0 < 1/x^2 := by positivity
  have hπ : 0 < Real.pi ^ ((1:ℝ)/4) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  have hyp : 0 < (1/x^2)^((5:ℝ)/4) :=
    Real.rpow_pos_of_pos hy _
  have hup : 0 < (1+x*u)^((5:ℝ)/4) :=
    Real.rpow_pos_of_pos hu _
  have hvp : 0 < (1+x*v)^((5:ℝ)/4) :=
    Real.rpow_pos_of_pos hv _
  have hmul :
      ((1/x^2)*(1+x*u)*(1+x*v))^((5:ℝ)/4) =
      (1/x^2)^((5:ℝ)/4) *
        (1+x*u)^((5:ℝ)/4) *
        (1+x*v)^((5:ℝ)/4) := by
    rw [Real.mul_rpow (mul_pos hy hu).le hv.le,
      Real.mul_rpow hy.le hu.le]
  rw [hmul]
  field_simp [ne_of_gt hyp, ne_of_gt hup, ne_of_gt hvp,
    ne_of_gt hπ] <;> ring

/-- The already proved actual Psi1 gamma series, renamed as
an exact function of the positive y-coordinate. -/
noncomputable def thetaClosedYSeries (y : ℝ) : ℝ :=
  ∑' n : ℕ, 2 * (n:ℝ)^2 * y^((5:ℝ)/4) *
    (Real.exp (-(n:ℝ)^2*y) -
      (1/4:ℝ) *
        (∫ v in Set.Ioi (1:ℝ),
          v^((1:ℝ)/4) * Real.exp (-(n:ℝ)^2*y*v)))

/-- For ALL admissible local Taylor shifts, the genuine
original normalizedKernel equals the prefactor times
the genuine, already-integrated theta closed series.
There is no assumed kernel transform or differentiation. -/
theorem normalizedKernel_eq_true_theta_closed_series
    (x u v : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    normalizedKernel x u v =
      (2 * Real.pi ^ ((1:ℝ)/4) * Real.exp (1/x^2) /
        (1/x^2)^((5:ℝ)/4)) *
      (Real.exp (u/x) * Real.exp (v/x) /
        ((1+x*u)^((5:ℝ)/4) * (1+x*v)^((5:ℝ)/4))) *
      (1/(4 * Real.pi ^ ((1:ℝ)/4))) *
      thetaClosedYSeries
        (Real.pi * Real.exp
          (4*(thetaTimeOfX x +
            Real.log (1+x*u)/4 + Real.log (1+x*v)/4))) := by
  let t : ℝ := thetaTimeOfX x +
    Real.log (1+x*u)/4 + Real.log (1+x*v)/4
  have ht : 1 ≤ Real.pi * Real.exp (4*t) :=
    theta_shifted_y_ge_one_on_box x u v hx hxB hu hv
  have hpsi : Psi1 t =
      (1/(4 * Real.pi ^ ((1:ℝ)/4))) *
        thetaClosedYSeries (Real.pi * Real.exp (4*t)) := by
    simpa only [thetaClosedYSeries] using
      (Psi1_eq_theta_closed_form_of_y_ge_one t ht)
  change
    (2 * Real.pi ^ ((1:ℝ)/4) * Real.exp (1/x^2) /
      (1/x^2)^((5:ℝ)/4)) *
    (Real.exp (u/x) * Real.exp (v/x) /
      ((1+x*u)^((5:ℝ)/4) * (1+x*v)^((5:ℝ)/4))) *
    Psi1 t = _
  rw [hpsi]
  dsimp [t]
  ring

end W5
