import W5.PhiSecondDerivative
import W5.PsiThirdDerivative
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Third derivative of the original theta series

An explicit, locally uniformly summable Gaussian-polynomial bound for
the third derivative permits a genuine differentiation of the second
derivative series. This extends the original theta primitive Psi1
through order four. It does NOT assert any W2–W5 determinant sign.
-/

namespace W5

/-- Third derivative of an individual original theta summand. -/
noncomputable def phiSummandThirdDerivative (n : ℕ) (t : ℝ) : ℝ :=
  (-128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*t) +
    1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*t) -
    4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*t) +
    3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*t) -
    375 * (n : ℝ)^2 * Real.pi * Real.exp (5*t)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))

/-- Explicit differentiation of the SECOND original theta summand derivative. -/
theorem phiSummandSecondDerivative_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (phiSummandSecondDerivative n)
      (phiSummandThirdDerivative n t) t := by
  have hlin17 : HasDerivAt (fun s : ℝ => (17:ℝ)*s) 17 t := by
    simpa using (hasDerivAt_id t).const_mul (17:ℝ)
  have hlin13 : HasDerivAt (fun s : ℝ => (13:ℝ)*s) 13 t := by
    simpa using (hasDerivAt_id t).const_mul (13:ℝ)
  have hlin9 : HasDerivAt (fun s : ℝ => (9:ℝ)*s) 9 t := by
    simpa using (hasDerivAt_id t).const_mul (9:ℝ)
  have hlin5 : HasDerivAt (fun s : ℝ => (5:ℝ)*s) 5 t := by
    simpa using (hasDerivAt_id t).const_mul (5:ℝ)
  have hlin4 : HasDerivAt (fun s : ℝ => (4:ℝ)*s) 4 t := by
    simpa using (hasDerivAt_id t).const_mul (4:ℝ)
  have h17 : HasDerivAt (fun s : ℝ => Real.exp (17*s))
      (Real.exp (17*t)*17) t :=
    (Real.hasDerivAt_exp (17*t)).comp t hlin17
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
        32 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*s) -
        224 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*s) +
        330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*s) -
        75 * (n : ℝ)^2 * Real.pi * Real.exp (5*s))
      (32 * (n : ℝ)^8 * Real.pi^4 * (Real.exp (17*t)*17) -
        224 * (n : ℝ)^6 * Real.pi^3 * (Real.exp (13*t)*13) +
        330 * (n : ℝ)^4 * Real.pi^2 * (Real.exp (9*t)*9) -
        75 * (n : ℝ)^2 * Real.pi * (Real.exp (5*t)*5)) t := by
    convert
      (((h17.const_mul (32 * (n : ℝ)^8 * Real.pi^4)).sub
        (h13.const_mul (224 * (n : ℝ)^6 * Real.pi^3))).add
        (h9.const_mul (330 * (n : ℝ)^4 * Real.pi^2))).sub
        (h5.const_mul (75 * (n : ℝ)^2 * Real.pi))
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
  have h21exp : Real.exp (21*t) =
      Real.exp (17*t)*Real.exp (4*t) := by
    rw [show (21:ℝ)*t = 17*t + 4*t by ring, Real.exp_add]
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
    simp only [phiSummandSecondDerivative, Pi.mul_apply]
  · simp only [phiSummandThirdDerivative]
    rw [h21exp, h17exp, h13exp, h9exp]
    ring

/-- Gaussian decay makes the third differentiated series absolutely summable. -/
theorem phiSummandThirdDerivative_summable (t : ℝ) :
    Summable (fun n : ℕ => phiSummandThirdDerivative n t) := by
  let a : ℝ := Real.pi * Real.exp (4*t)
  have ha : 0 < a := mul_pos Real.pi_pos (Real.exp_pos _)
  have h10 : Summable (fun n : ℕ =>
      (n : ℝ)^10 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 10 a ha
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
    ((((h10.mul_left (-128 * Real.pi^5 * Real.exp (21*t))).add
      (h8.mul_left (1440 * Real.pi^4 * Real.exp (17*t)))).sub
      (h6.mul_left (4232 * Real.pi^3 * Real.exp (13*t)))).add
      (h4.mul_left (3270 * Real.pi^2 * Real.exp (9*t)))).sub
      (h2.mul_left (375 * Real.pi * Real.exp (5*t)))
  convert hs using 1
  funext n
  simp only [phiSummandThirdDerivative]
  have heq : -a * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*t) := by
    dsimp [a]
    ring
  rw [heq]
  ring

/-- Uniform summable majorant for the third derivative on [a,b]. -/
noncomputable def phiThirdDerivativeEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  (128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b) +
    1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) +
    4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
    3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
    375 * (n : ℝ)^2 * Real.pi * Real.exp (5*b)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a))

theorem phiThirdDerivativeEnvelope_summable (a b : ℝ) :
    Summable (phiThirdDerivativeEnvelope a b) := by
  let q : ℝ := Real.pi * Real.exp (4*a)
  have hq : 0 < q := mul_pos Real.pi_pos (Real.exp_pos _)
  have h10 : Summable (fun n : ℕ =>
      (n : ℝ)^10 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 10 q hq
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
    ((((h10.mul_left (128 * Real.pi^5 * Real.exp (21*b))).add
      (h8.mul_left (1440 * Real.pi^4 * Real.exp (17*b)))).add
      (h6.mul_left (4232 * Real.pi^3 * Real.exp (13*b)))).add
      (h4.mul_left (3270 * Real.pi^2 * Real.exp (9*b)))).add
      (h2.mul_left (375 * Real.pi * Real.exp (5*b)))
  convert hs using 1
  funext n
  dsimp [phiThirdDerivativeEnvelope, q]
  rw [show -(Real.pi * Real.exp (4*a)) * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*a) by ring]
  ring

/-- Locally uniform dominance allows termwise differentiation once more. -/
theorem phiSummandThirdDerivative_le_envelope
    (a b x : ℝ) (n : ℕ)
    (hax : a ≤ x) (hxb : x ≤ b) :
    ‖phiSummandThirdDerivative n x‖ ≤
      phiThirdDerivativeEnvelope a b n := by
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
  have h21 : Real.exp (21*x) ≤ Real.exp (21*b) :=
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
  have h21' :
      128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) ≤
      128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b) :=
    mul_le_mul_of_nonneg_left h21 (by positivity)
  have h17' :
      1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) ≤
      1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) :=
    mul_le_mul_of_nonneg_left h17 (by positivity)
  have h13' :
      4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) ≤
      4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) :=
    mul_le_mul_of_nonneg_left h13 (by positivity)
  have h9' :
      3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) ≤
      3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) :=
    mul_le_mul_of_nonneg_left h9 (by positivity)
  have h5' :
      375 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) ≤
      375 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have hpoly :
      128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) +
        1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) +
        4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
        375 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) ≤
      128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b) +
        1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) +
        4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
        3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
        375 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) := by
    linarith
  have hn21 :
      0 ≤ 128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) := by positivity
  have hn17 :
      0 ≤ 1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) := by positivity
  have hn13 :
      0 ≤ 4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) := by positivity
  have hn9 :
      0 ≤ 3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) := by positivity
  have hn5 :
      0 ≤ 375 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) := by positivity
  have habs :
      |(-128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) +
        1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) -
        4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) -
        375 * (n : ℝ)^2 * Real.pi * Real.exp (5*x))| ≤
      128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) +
        1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) +
        4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
        3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
        375 * (n : ℝ)^2 * Real.pi * Real.exp (5*x) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnonneg :
      0 ≤ 128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b) +
        1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) +
        4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
        3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
        375 * (n : ℝ)^2 * Real.pi * Real.exp (5*b) := by
    positivity
  calc
    ‖phiSummandThirdDerivative n x‖ =
        |(-128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) +
          1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) -
          4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
          3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) -
          375 * (n : ℝ)^2 * Real.pi * Real.exp (5*x))| *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) := by
          simp only [Real.norm_eq_abs, phiSummandThirdDerivative,
            abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) +
          1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) +
          4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) +
          3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) +
          375 * (n : ℝ)^2 * Real.pi * Real.exp (5*x)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) :=
          mul_le_mul_of_nonneg_right habs (le_of_lt (Real.exp_pos _))
    _ ≤ (128 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b) +
          1440 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) +
          4232 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) +
          3270 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) +
          375 * (n : ℝ)^2 * Real.pi * Real.exp (5*b)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a)) := by
          exact mul_le_mul hpoly hdecay
            (le_of_lt (Real.exp_pos _)) hnonneg
    _ = phiThirdDerivativeEnvelope a b n := rfl

/-- The second derivative of the ORIGINAL infinite theta series
has the third derivative obtained by summing the derivatives of its
genuine terms; no analytical interchange hypothesis is assumed. -/
theorem Phi_second_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 2 Phi)
      (∑' n : ℕ, phiSummandThirdDerivative n t) t := by
  have ht : t ∈ Set.Ioo (t-1) (t+1) := by
    constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (phiThirdDerivativeEnvelope_summable (t-1) (t+1))
    isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => phiSummandSecondDerivative_hasDerivAt n s)
    (fun n s hs => phiSummandThirdDerivative_le_envelope
      (t-1) (t+1) s n hs.1.le hs.2.le)
    ht (phiSummandSecondDerivative_summable t) ht
  have hfun :
      (fun s : ℝ => ∑' n : ℕ, phiSummandSecondDerivative n s) =
        iteratedDeriv 2 Phi := by
    funext s
    exact (Phi_secondDerivative s).symm
  rw [hfun] at h
  exact h

theorem Phi_thirdDerivative (t : ℝ) :
    iteratedDeriv 3 Phi t =
      ∑' n : ℕ, phiSummandThirdDerivative n t := by
  rw [show (3:ℕ) = 2+1 by omega, iteratedDeriv_succ]
  exact (Phi_second_hasDerivAt t).deriv

theorem Phi_second_differentiable :
    Differentiable ℝ (iteratedDeriv 2 Phi) := by
  intro t
  exact (Phi_second_hasDerivAt t).differentiableAt

/-- Exact fourth derivative of the ORIGINAL integrated theta kernel. -/
theorem Psi1_third_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 3 Psi1)
      (-(∑' n : ℕ, phiSummandThirdDerivative n t)) t := by
  have hthird : iteratedDeriv 3 Psi1 =
      fun s : ℝ => -(iteratedDeriv 2 Phi s) := by
    funext s
    rw [Psi1_third_derivative, Phi_secondDerivative]
  rw [hthird]
  exact (Phi_second_hasDerivAt t).neg

theorem Psi1_fourth_derivative (t : ℝ) :
    iteratedDeriv 4 Psi1 t =
      -(∑' n : ℕ, phiSummandThirdDerivative n t) := by
  rw [show (4:ℕ) = 3+1 by omega, iteratedDeriv_succ]
  exact (Psi1_third_hasDerivAt t).deriv

theorem Psi1_third_differentiable :
    Differentiable ℝ (iteratedDeriv 3 Psi1) := by
  intro t
  exact (Psi1_third_hasDerivAt t).differentiableAt

end W5
