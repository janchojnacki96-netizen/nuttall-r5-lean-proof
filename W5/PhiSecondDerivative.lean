import W5.PhiFirstDerivative
import W5.PsiFundamentalDerivative
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Genuine second derivative of the original Riemann theta series

We differentiate the real n-th summand explicitly, prove a summable
Gaussian majorant for its SECOND derivative uniformly on a bounded
interval, then apply Mathlib's termwise differentiation theorem.

The resulting statement is unconditional on all real t:
  Phi''(t) = sum_n phiSummandSecondDerivative(n,t).
Consequently Psi1'''(t) = -Phi''(t).

No assumption about signs of Wronskians or numerical certificates
enters this proof.
-/

namespace W5

/-- Explicit second derivative of the original theta summand. -/
noncomputable def phiSummandSecondDerivative (n : ℕ) (t : ℝ) : ℝ :=
  (32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*t) -
    224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*t) +
    330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*t) -
    75 * (n : ℝ)^2 * Real.pi * Real.exp (5*t)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))

/-- Each genuine first-derivative summand is differentiable again. -/
theorem phiSummandDerivative_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (phiSummandDerivative n)
      (phiSummandSecondDerivative n t) t := by
  have hlin13 : HasDerivAt (fun s : ℝ => (13:ℝ)*s) 13 t := by
    simpa using (hasDerivAt_id t).const_mul (13:ℝ)
  have hlin9 : HasDerivAt (fun s : ℝ => (9:ℝ)*s) 9 t := by
    simpa using (hasDerivAt_id t).const_mul (9:ℝ)
  have hlin5 : HasDerivAt (fun s : ℝ => (5:ℝ)*s) 5 t := by
    simpa using (hasDerivAt_id t).const_mul (5:ℝ)
  have hlin4 : HasDerivAt (fun s : ℝ => (4:ℝ)*s) 4 t := by
    simpa using (hasDerivAt_id t).const_mul (4:ℝ)
  have h13 : HasDerivAt (fun s : ℝ => Real.exp (13*s))
      (Real.exp (13*t)*13) t :=
    (Real.hasDerivAt_exp (13*t)).comp t hlin13
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
        -8 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*s) +
        30 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*s) -
        15 * (n : ℝ)^2 * Real.pi * Real.exp (5*s))
      (-8 * (n : ℝ)^6 * Real.pi^3 * (Real.exp (13*t)*13) +
        30 * (n : ℝ)^4 * Real.pi^2 * (Real.exp (9*t)*9) -
        15 * (n : ℝ)^2 * Real.pi * (Real.exp (5*t)*5)) t := by
    convert
      ((h13.const_mul (-8 * (n : ℝ)^6 * Real.pi^3)).add
        (h9.const_mul (30 * (n : ℝ)^4 * Real.pi^2))).sub
          (h5.const_mul (15 * (n : ℝ)^2 * Real.pi))
      using 1 <;> ring
  have hlinE : HasDerivAt
      (fun s : ℝ => -((n : ℝ)^2 * Real.pi) * Real.exp (4*s))
      (-((n : ℝ)^2 * Real.pi) * (Real.exp (4*t)*4)) t := by
    convert h4.const_mul (-((n : ℝ)^2 * Real.pi)) using 1 <;> ring
  have harg (s : ℝ) :
      -(n : ℝ)^2 * Real.pi * Real.exp (4*s) =
        -((n : ℝ)^2 * Real.pi) * Real.exp (4*s) := by ring
  have hE' : HasDerivAt
      (fun s : ℝ =>
        Real.exp (-((n : ℝ)^2 * Real.pi) * Real.exp (4*s)))
      (Real.exp (-((n : ℝ)^2 * Real.pi) * Real.exp (4*t)) *
        (-((n : ℝ)^2 * Real.pi) * (Real.exp (4*t)*4))) t := by
    have houter : HasDerivAt Real.exp
        (Real.exp (-((n : ℝ)^2 * Real.pi) * Real.exp (4*t)))
        (-((n : ℝ)^2 * Real.pi) * Real.exp (4*t)) :=
      Real.hasDerivAt_exp _
    simpa only [Function.comp_def] using (houter.comp t hlinE)
  have hE : HasDerivAt
      (fun s : ℝ =>
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*s)))
      (Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t)) *
        (-((n : ℝ)^2 * Real.pi) * (Real.exp (4*t)*4))) t := by
    simpa only [harg] using hE'
  have h17exp : Real.exp (17*t) =
      Real.exp (13*t)*Real.exp (4*t) := by
    rw [show (17:ℝ)*t = 13*t + 4*t by ring, Real.exp_add]
  have h13exp : Real.exp (13*t) =
      Real.exp (9*t)*Real.exp (4*t) := by
    rw [show (13:ℝ)*t = 9*t + 4*t by ring, Real.exp_add]
  have h9exp : Real.exp (9*t) =
      Real.exp (5*t)*Real.exp (4*t) := by
    rw [show (9:ℝ)*t = 5*t + 4*t by ring, Real.exp_add]
  have hprod := hA.mul hE
  convert hprod using 1
  · funext s
    simp only [phiSummandDerivative, Pi.mul_apply]
  · simp only [phiSummandSecondDerivative]
    rw [h17exp, h13exp, h9exp]
    ring

/-- The second-derivative theta series converges absolutely. -/
theorem phiSummandSecondDerivative_summable (t : ℝ) :
    Summable (fun n : ℕ => phiSummandSecondDerivative n t) := by
  let a : ℝ := Real.pi * Real.exp (4*t)
  have ha : 0 < a := mul_pos Real.pi_pos (Real.exp_pos _)
  have h8 : Summable (fun n : ℕ =>
      (n : ℝ)^8 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 8 a ha
  have h6 : Summable (fun n : ℕ =>
      (n : ℝ)^6 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 6 a ha
  have h4 : Summable (fun n : ℕ =>
      (n : ℝ)^4 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 4 a ha
  have h2 : Summable (fun n : ℕ =>
      (n : ℝ)^2 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 2 a ha
  have hs :=
    (((h8.mul_left (32 * Real.pi^4 * Real.exp (17*t))).sub
      (h6.mul_left (224 * Real.pi^3 * Real.exp (13*t)))).add
        (h4.mul_left (330 * Real.pi^2 * Real.exp (9*t)))).sub
          (h2.mul_left (75 * Real.pi * Real.exp (5*t)))
  convert hs using 1
  funext n
  simp only [phiSummandSecondDerivative]
  have heq : -a * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*t) := by
    dsimp [a]
    ring
  rw [heq]
  ring

/-- Gaussian-polynomial envelope uniform on [a,b]. -/
noncomputable def phiSecondDerivativeEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  (32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) +
    224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
    330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
    75 * (n : ℝ)^2 * Real.pi * Real.exp (5*b)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a))

/-- The envelope is summable over the square indices. -/
theorem phiSecondDerivativeEnvelope_summable (a b : ℝ) :
    Summable (phiSecondDerivativeEnvelope a b) := by
  let q : ℝ := Real.pi * Real.exp (4*a)
  have hq : 0 < q := mul_pos Real.pi_pos (Real.exp_pos _)
  have h8 : Summable (fun n : ℕ =>
      (n : ℝ)^8 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 8 q hq
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
    (((h8.mul_left (32 * Real.pi^4 * Real.exp (17*b))).add
      (h6.mul_left (224 * Real.pi^3 * Real.exp (13*b)))).add
        (h4.mul_left (330 * Real.pi^2 * Real.exp (9*b)))).add
          (h2.mul_left (75 * Real.pi * Real.exp (5*b)))
  convert hs using 1
  funext n
  dsimp [phiSecondDerivativeEnvelope, q]
  rw [show -(Real.pi * Real.exp (4*a)) * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*a) by ring]
  ring

/-- Uniform norm bound for every second-derivative theta summand. -/
theorem phiSummandSecondDerivative_le_envelope
    (a b x : ℝ) (n : ℕ)
    (hax : a ≤ x) (hxb : x ≤ b) :
    ‖phiSummandSecondDerivative n x‖ ≤
      phiSecondDerivativeEnvelope a b n := by
  have h4 : Real.exp (4*a) ≤ Real.exp (4*x) :=
    Real.exp_le_exp.mpr (by linarith)
  have h5 : Real.exp (5*x) ≤ Real.exp (5*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9 : Real.exp (9*x) ≤ Real.exp (9*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h13 : Real.exp (13*x) ≤ Real.exp (13*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h17 : Real.exp (17*x) ≤ Real.exp (17*b) :=
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
  have h17' :
      32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) ≤
      32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) :=
    mul_le_mul_of_nonneg_left h17 (by positivity)
  have h13' :
      224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) ≤
      224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) :=
    mul_le_mul_of_nonneg_left h13 (by positivity)
  have h9' :
      330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) ≤
      330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) :=
    mul_le_mul_of_nonneg_left h9 (by positivity)
  have h5' :
      75 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) ≤
      75 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have hpoly :
      32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) +
        224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
        75 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) ≤
      32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) +
        224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
        330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
        75 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) := by
    linarith
  have hn17 :
      0 ≤ 32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) := by positivity
  have hn13 :
      0 ≤ 224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) := by positivity
  have hn9 :
      0 ≤ 330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) := by positivity
  have hn5 :
      0 ≤ 75 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) := by positivity
  have habs :
      |(32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) -
        224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) -
        75 * (n : ℝ)^2 * Real.pi * Real.exp (5*x))| ≤
      32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) +
        224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
        75 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnonneg :
      0 ≤ 32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) +
        224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
        330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
        75 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) := by
    positivity
  calc
    ‖phiSummandSecondDerivative n x‖ =
        |(32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) -
          224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
          330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) -
          75 * (n : ℝ)^2 * Real.pi * Real.exp (5*x))| *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) := by
          simp only [Real.norm_eq_abs, phiSummandSecondDerivative,
            abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) +
          224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
          330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
          75 * (n : ℝ)^2 * Real.pi * Real.exp (5*x)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) :=
          mul_le_mul_of_nonneg_right habs (le_of_lt (Real.exp_pos _))
    _ ≤ (32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) +
          224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
          330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
          75 * (n : ℝ)^2 * Real.pi * Real.exp (5*b)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a)) := by
          exact mul_le_mul hpoly hdecay
            (le_of_lt (Real.exp_pos _)) hnonneg
    _ = phiSecondDerivativeEnvelope a b n := rfl

/-- The second derivative of the ORIGINAL Phi equals the convergent
sum of the genuine second derivatives. -/
theorem Phi_secondDerivative (t : ℝ) :
    iteratedDeriv 2 Phi t =
      ∑' n : ℕ, phiSummandSecondDerivative n t := by
  have ht : t ∈ Set.Ioo (t-1) (t+1) := by
    constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (phiSecondDerivativeEnvelope_summable (t-1) (t+1))
    isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => phiSummandDerivative_hasDerivAt n s)
    (fun n s hs => phiSummandSecondDerivative_le_envelope
      (t-1) (t+1) s n hs.1.le hs.2.le)
    ht (phiSummandDerivative_summable t) ht
  have hfun :
      (fun s : ℝ => ∑' n : ℕ, phiSummandDerivative n s) =
        deriv Phi := by
    funext s
    exact (Phi_hasDerivAt s).deriv.symm
  rw [hfun] at h
  rw [show (2:ℕ)=1+1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  exact h.deriv

end W5
