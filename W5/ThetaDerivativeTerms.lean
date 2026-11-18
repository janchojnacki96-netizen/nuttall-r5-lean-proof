import W5.ThetaPhiSummability
import W5.ThetaCoordinateAlgebra
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# First derivatives of the ORIGINAL theta summands

These are actual derivatives of the terms defining `W5.Phi`.
The resulting differentiated series is absolutely summable at each
real argument. This alone is *not* a termwise differentiation theorem:
local uniform derivative bounds are a separate obligation.
-/

namespace W5

/-- Explicit first derivative of the original Riemann theta summand. -/
noncomputable def phiSummandDerivative (n : ℕ) (t : ℝ) : ℝ :=
  (-8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*t) +
    30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*t) -
    15 * (n : ℝ)^2 * Real.pi * Real.exp (5*t)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))

/-- Exact derivative by chain and product rules, with no extra assumptions. -/
theorem phiSummand_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (phiSummand n) (phiSummandDerivative n t) t := by
  have hlin9 : HasDerivAt (fun s : ℝ => (9:ℝ)*s) 9 t := by
    simpa using (hasDerivAt_id t).const_mul (9:ℝ)
  have hlin5 : HasDerivAt (fun s : ℝ => (5:ℝ)*s) 5 t := by
    simpa using (hasDerivAt_id t).const_mul (5:ℝ)
  have hlin4 : HasDerivAt (fun s : ℝ => (4:ℝ)*s) 4 t := by
    simpa using (hasDerivAt_id t).const_mul (4:ℝ)
  have h9 : HasDerivAt (fun s : ℝ => Real.exp (9*s))
      (Real.exp (9*t)*9) t :=
    (Real.hasDerivAt_exp (9*t)).comp t hlin9
  have h5 : HasDerivAt (fun s : ℝ => Real.exp (5*s))
      (Real.exp (5*t)*5) t :=
    (Real.hasDerivAt_exp (5*t)).comp t hlin5
  have h4 : HasDerivAt (fun s : ℝ => Real.exp (4*s))
      (Real.exp (4*t)*4) t :=
    (Real.hasDerivAt_exp (4*t)).comp t hlin4
  have hA : HasDerivAt
      (fun s : ℝ =>
        2 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*s) -
        3 * (n : ℝ)^2 * Real.pi * Real.exp (5*s))
      (2 * (n : ℝ)^4 * Real.pi^2 * (Real.exp (9*t)*9) -
        3 * (n : ℝ)^2 * Real.pi * (Real.exp (5*t)*5)) t := by
    convert
      (h9.const_mul (2 * (n : ℝ)^4 * Real.pi^2)).sub
        (h5.const_mul (3 * (n : ℝ)^2 * Real.pi))
      using 1 <;> ring
  have hlinE : HasDerivAt
      (fun s : ℝ => -(n : ℝ)^2 * Real.pi * Real.exp (4*s))
      (-((n : ℝ)^2 * Real.pi) * (Real.exp (4*t)*4)) t := by
    convert h4.const_mul (-((n : ℝ)^2 * Real.pi)) using 1 <;> ring
  have hE : HasDerivAt
      (fun s : ℝ =>
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*s)))
      (Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t)) *
        (-((n : ℝ)^2 * Real.pi) * (Real.exp (4*t)*4))) t :=
    (Real.hasDerivAt_exp
      (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))).comp t hlinE
  have h13 : Real.exp (13*t) =
      Real.exp (9*t)*Real.exp (4*t) := by
    rw [show (13:ℝ)*t = 9*t + 4*t by ring, Real.exp_add]
  have h9' : Real.exp (9*t) =
      Real.exp (5*t)*Real.exp (4*t) := by
    rw [show (9:ℝ)*t = 5*t + 4*t by ring, Real.exp_add]
  have hprod := hA.mul hE
  convert hprod using 1
  · funext s
    simp only [phiSummand, Pi.mul_apply]
    ring
  · simp only [phiSummandDerivative]
    rw [h13, h9']
    ring

/-- Absolute convergence of the genuine first-derivative theta series. -/
theorem phiSummandDerivative_summable (t : ℝ) :
    Summable (fun n : ℕ => phiSummandDerivative n t) := by
  let a : ℝ := Real.pi * Real.exp (4*t)
  have ha : 0 < a := mul_pos Real.pi_pos (Real.exp_pos _)
  have h6 : Summable (fun n : ℕ =>
      (n : ℝ)^6 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 6 a ha
  have h4 : Summable (fun n : ℕ =>
      (n : ℝ)^4 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 4 a ha
  have h2 : Summable (fun n : ℕ =>
      (n : ℝ)^2 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 2 a ha
  have hsum :=
    ((h6.mul_left (-8 * Real.pi^3 * Real.exp (13*t))).add
      (h4.mul_left (30 * Real.pi^2 * Real.exp (9*t)))).sub
        (h2.mul_left (15 * Real.pi * Real.exp (5*t)))
  convert hsum using 1
  funext n
  simp only [phiSummandDerivative]
  have heq : -a * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*t) := by
    dsimp [a]
    ring
  rw [heq]
  ring

end W5
