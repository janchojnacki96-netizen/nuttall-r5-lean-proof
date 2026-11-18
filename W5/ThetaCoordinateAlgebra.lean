import W5.Statement
import W5.ThetaCoordinateIdentity

/-!
# Exact algebra and calculus for the theta change of coordinates

These are unconditional real-number identities. They support, but
do not establish, the analytic equality between the theta-integral
and the certificate's coefficient matrix.
-/

namespace W5

/-- Rewrites the original n-th theta summand in terms of y=pi*exp(4t). -/
theorem phiSummand_factor (n : ℕ) (t : ℝ) :
    phiSummand n t =
      (n:ℝ)^2 * Real.pi * Real.exp (5*t) *
      (2*(n:ℝ)^2*Real.pi*Real.exp (4*t)-3) *
      Real.exp (-(n:ℝ)^2*Real.pi*Real.exp (4*t)) := by
  have harg : (9:ℝ)*t = (5:ℝ)*t + 4*t := by ring
  have hexp : Real.exp (9*t) = Real.exp (5*t)*Real.exp (4*t) := by
    rw [harg, Real.exp_add]
  unfold phiSummand
  rw [hexp]
  ring

/-- The change of variable y(t)=pi*exp(4t) has strictly positive Jacobian. -/
theorem theta_y_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.pi * Real.exp (4*s))
      (4*Real.pi*Real.exp (4*t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => (4:ℝ)*s) 4 t := by
    simpa using (hasDerivAt_id t).const_mul (4:ℝ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (4*s))
      (Real.exp (4*t)*4) t :=
    (Real.hasDerivAt_exp (4*t)).comp t hlin
  convert hexp.const_mul Real.pi using 1 <;> ring

/-- The t-coordinate used in the normalized kernel indeed corresponds to y=1/x². -/
theorem theta_base_coordinate (x : ℝ) (hx : 0 < x) :
    Real.pi * Real.exp (4*(Real.log ((1/x^2)/Real.pi)/4)) = 1/x^2 := by
  have hy : (0:ℝ) < (1/x^2)/Real.pi :=
    div_pos (div_pos (by norm_num) (sq_pos_of_pos hx)) Real.pi_pos
  have harg : 4*(Real.log ((1/x^2)/Real.pi)/4) =
      Real.log ((1/x^2)/Real.pi) := by ring
  rw [harg, Real.exp_log hy]
  field_simp [ne_of_gt hx, ne_of_gt Real.pi_pos]

/-- The universal algebraic identity producing K_{p,w}(u,v). -/
theorem theta_gauge_exponent_identity
    (p w x u v : ℝ) (hx : x ≠ 0) :
    (u+v)/x -
        ((p+w*x^2)/x^2)*((1+x*u)*(1+x*v)-1) =
      -(((p-1)/x)+w*x)*(u+v) - (p+w*x^2)*u*v := by
  field_simp [hx] <;> ring

/-- Consequently, the gauged exponential is the kernel used in the certificate. -/
theorem theta_gauged_exp_kernel
    (p w x u v : ℝ) (hx : x ≠ 0) :
    Real.exp ((u+v)/x -
        ((p+w*x^2)/x^2)*((1+x*u)*(1+x*v)-1)) =
      Real.exp (-(((p-1)/x)+w*x)*(u+v) -
        (p+w*x^2)*u*v) := by
  rw [theta_gauge_exponent_identity p w x u v hx]

end W5
