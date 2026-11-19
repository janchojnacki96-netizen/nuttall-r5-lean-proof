import W5.Statement

/-!
An exact exponential/logarithmic identity needed for the change of
coordinates in the Nuttall theta kernel. This is an elementary
component of the analytic transform; exchanging infinite sums,
integrals and derivatives remains to be proved.
-/

namespace W5

theorem theta_coordinate_exp_identity (x t u v : ℝ)
    (hu : 0 < 1 + x*u) (hv : 0 < 1 + x*v) :
    Real.pi * Real.exp
        (4 * (t + Real.log (1+x*u)/4 + Real.log (1+x*v)/4)) =
      (Real.pi * Real.exp (4*t)) * (1+x*u) * (1+x*v) := by
  have ha : Real.exp (Real.log (1+x*u)) = 1+x*u :=
    Real.exp_log hu
  have hb : Real.exp (Real.log (1+x*v)) = 1+x*v :=
    Real.exp_log hv
  have harg :
      4 * (t + Real.log (1+x*u)/4 + Real.log (1+x*v)/4) =
        (4*t + Real.log (1+x*u)) + Real.log (1+x*v) := by ring
  rw [harg, Real.exp_add, Real.exp_add, ha, hb]
  ring

end W5
