import W5.ThetaDerivativeTerms
import W5.ThetaPhiSummability
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Locally uniform differentiation of the original theta series

For an arbitrary bounded interval [a,b] a Gaussian-polynomial sequence
dominates the absolute value of every first theta-summand derivative.
This provides the *uniform* hypothesis needed by Mathlib's theorem on
differentiating an infinite sum. The resulting theorem is about the
original `W5.Phi` on the entire real line.
-/

namespace W5

/-- Explicit summable Gaussian majorant for the differentiated theta series
on an arbitrary bounded real interval [a,b]. -/
noncomputable def phiDerivativeEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  (8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
   30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
   15 * (n : ℝ)^2 * Real.pi * Real.exp (5*b)) *
    Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a))

theorem phiDerivativeEnvelope_summable (a b : ℝ) :
    Summable (phiDerivativeEnvelope a b) := by
  let q : ℝ := Real.pi * Real.exp (4*a)
  have hq : 0 < q := mul_pos Real.pi_pos (Real.exp_pos _)
  have h6 : Summable (fun n : ℕ =>
      (n : ℝ)^6 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 6 q hq
  have h4 : Summable (fun n : ℕ =>
      (n : ℝ)^4 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 4 q hq
  have h2 : Summable (fun n : ℕ =>
      (n : ℝ)^2 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 2 q hq
  have hs :=
    ((h6.mul_left (8 * Real.pi^3 * Real.exp (13*b))).add
      (h4.mul_left (30 * Real.pi^2 * Real.exp (9*b)))).add
        (h2.mul_left (15 * Real.pi * Real.exp (5*b)))
  convert hs using 1
  funext n
  dsimp [phiDerivativeEnvelope, q]
  rw [show -(Real.pi * Real.exp (4*a)) * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*a) by ring]
  ring

/-- Uniform estimate: every derivative is bounded by a single
summable sequence on the entire closed interval [a,b]. -/
theorem phiSummandDerivative_le_envelope (a b x : ℝ) (n : ℕ)
    (hax : a ≤ x) (hxb : x ≤ b) :
    ‖phiSummandDerivative n x‖ ≤ phiDerivativeEnvelope a b n := by
  have h4 : Real.exp (4*a) ≤ Real.exp (4*x) :=
    Real.exp_le_exp.mpr (by linarith)
  have h5 : Real.exp (5*x) ≤ Real.exp (5*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9 : Real.exp (9*x) ≤ Real.exp (9*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h13 : Real.exp (13*x) ≤ Real.exp (13*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have hp : 0 ≤ (n : ℝ)^2 * Real.pi := by positivity
  have hneg :
      -((n : ℝ)^2 * Real.pi) * Real.exp (4*x) ≤
      -((n : ℝ)^2 * Real.pi) * Real.exp (4*a) :=
    mul_le_mul_of_nonpos_left h4 (by linarith)
  have hdecay :
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) ≤
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a)) := by
    apply Real.exp_le_exp.mpr
    convert hneg using 1 <;> ring
  have h13' :
      8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) ≤
      8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) :=
    mul_le_mul_of_nonneg_left h13 (by positivity)
  have h9' :
      30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) ≤
      30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) :=
    mul_le_mul_of_nonneg_left h9 (by positivity)
  have h5' :
      15 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) ≤
      15 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have hpoly :
      8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
        15 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) ≤
      8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
        30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
        15 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) := by
    linarith
  have hn13 : 0 ≤
      8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) := by positivity
  have hn9 : 0 ≤
      30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) := by positivity
  have hn5 : 0 ≤
      15 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) := by positivity
  have habs :
      |(-8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) -
        15 * (n : ℝ)^2 * Real.pi * Real.exp (5*x))| ≤
      8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
        15 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnonneg :
      0 ≤ 8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
        30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
        15 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) := by
    positivity
  calc
    ‖phiSummandDerivative n x‖ =
        |(-8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
          30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) -
          15 * (n : ℝ)^2 * Real.pi * Real.exp (5*x))| *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) := by
          simp only [Real.norm_eq_abs, phiSummandDerivative,
            abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
          30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
          15 * (n : ℝ)^2 * Real.pi * Real.exp (5*x)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) :=
          mul_le_mul_of_nonneg_right habs (le_of_lt (Real.exp_pos _))
    _ ≤ (8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
          30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
          15 * (n : ℝ)^2 * Real.pi * Real.exp (5*b)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a)) := by
          exact mul_le_mul hpoly hdecay
            (le_of_lt (Real.exp_pos _)) hnonneg
    _ = phiDerivativeEnvelope a b n := rfl

/-- The ORIGINAL theta function is differentiable by termwise differentiation.
The locally uniform majorant is proved above, not assumed. -/
theorem Phi_hasDerivAt (t : ℝ) :
    HasDerivAt Phi
      (∑' n : ℕ, phiSummandDerivative n t) t := by
  have ht : t ∈ Set.Ioo (t-1) (t+1) := by
    constructor <;> dsimp <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (phiDerivativeEnvelope_summable (t-1) (t+1))
    isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => phiSummand_hasDerivAt n s)
    (fun n s hs => phiSummandDerivative_le_envelope
      (t-1) (t+1) s n hs.1.le hs.2.le)
    ht (phiSummand_summable t) ht
  have hfun :
      (fun s : ℝ => ∑' n : ℕ, phiSummand n s) = Phi := by
    funext s
    exact (Phi_eq_tsum_phiSummand s).symm
  rw [hfun] at h
  exact h

theorem Phi_differentiable : Differentiable ℝ Phi := by
  intro t
  exact (Phi_hasDerivAt t).differentiableAt

end W5
