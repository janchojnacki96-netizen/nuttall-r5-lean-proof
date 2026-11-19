import W5.PhiFifthDerivative
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Original theta series: derivative order 6

This proof is about the actual Riemann theta series, not a surrogate.
It uses an explicit Gaussian-polynomial summable envelope on compact
intervals to justify differentiation under the infinite sum.
Nothing here asserts an order-6 Wronskian sign.
-/

namespace W5

noncomputable def phiSummandSixthDerivative (n : ℕ) (t : ℝ) : ℝ :=
  (8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*t)
        - 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*t)
        + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*t)
        - 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*t)
        + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*t)
        - 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*t)
        + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*t)
        - 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*t)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))

theorem phiSummandFifthDerivative_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (phiSummandFifthDerivative n)
      (phiSummandSixthDerivative n t) t := by
  have hlin29 : HasDerivAt (fun s : ℝ => (29:ℝ)*s) 29 t := by
    simpa using (hasDerivAt_id t).const_mul (29:ℝ)
  have h29 : HasDerivAt (fun s : ℝ => Real.exp (29*s))
      (Real.exp (29*t)*29) t :=
    (Real.hasDerivAt_exp (29*t)).comp t hlin29
  have hlin25 : HasDerivAt (fun s : ℝ => (25:ℝ)*s) 25 t := by
    simpa using (hasDerivAt_id t).const_mul (25:ℝ)
  have h25 : HasDerivAt (fun s : ℝ => Real.exp (25*s))
      (Real.exp (25*t)*25) t :=
    (Real.hasDerivAt_exp (25*t)).comp t hlin25
  have hlin21 : HasDerivAt (fun s : ℝ => (21:ℝ)*s) 21 t := by
    simpa using (hasDerivAt_id t).const_mul (21:ℝ)
  have h21 : HasDerivAt (fun s : ℝ => Real.exp (21*s))
      (Real.exp (21*t)*21) t :=
    (Real.hasDerivAt_exp (21*t)).comp t hlin21
  have hlin17 : HasDerivAt (fun s : ℝ => (17:ℝ)*s) 17 t := by
    simpa using (hasDerivAt_id t).const_mul (17:ℝ)
  have h17 : HasDerivAt (fun s : ℝ => Real.exp (17*s))
      (Real.exp (17*t)*17) t :=
    (Real.hasDerivAt_exp (17*t)).comp t hlin17
  have hlin13 : HasDerivAt (fun s : ℝ => (13:ℝ)*s) 13 t := by
    simpa using (hasDerivAt_id t).const_mul (13:ℝ)
  have h13 : HasDerivAt (fun s : ℝ => Real.exp (13*s))
      (Real.exp (13*t)*13) t :=
    (Real.hasDerivAt_exp (13*t)).comp t hlin13
  have hlin9 : HasDerivAt (fun s : ℝ => (9:ℝ)*s) 9 t := by
    simpa using (hasDerivAt_id t).const_mul (9:ℝ)
  have h9 : HasDerivAt (fun s : ℝ => Real.exp (9*s))
      (Real.exp (9*t)*9) t :=
    (Real.hasDerivAt_exp (9*t)).comp t hlin9
  have hlin5 : HasDerivAt (fun s : ℝ => (5:ℝ)*s) 5 t := by
    simpa using (hasDerivAt_id t).const_mul (5:ℝ)
  have h5 : HasDerivAt (fun s : ℝ => Real.exp (5*s))
      (Real.exp (5*t)*5) t :=
    (Real.hasDerivAt_exp (5*t)).comp t hlin5
  have hlin4 : HasDerivAt (fun s : ℝ => (4:ℝ)*s) 4 t := by
    simpa using (hasDerivAt_id t).const_mul (4:ℝ)
  have h4 : HasDerivAt (fun s : ℝ => Real.exp (4*s))
      (Real.exp (4*t)*4) t :=
    (Real.hasDerivAt_exp (4*t)).comp t hlin4
  have hA : HasDerivAt
      (fun s : ℝ =>
        -2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*s)
        + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*s)
        - 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*s)
        + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*s)
        - 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*s)
        + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*s)
        - 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*s))
      (-2048 * (n : ℝ)^14 * Real.pi^7 * (Real.exp (29*t)*29)
        + 46592 * (n : ℝ)^12 * Real.pi^6 * (Real.exp (25*t)*25)
        - 343040 * (n : ℝ)^10 * Real.pi^5 * (Real.exp (21*t)*21)
        + 976320 * (n : ℝ)^8 * Real.pi^4 * (Real.exp (17*t)*17)
        - 1008968 * (n : ℝ)^6 * Real.pi^3 * (Real.exp (13*t)*13)
        + 285870 * (n : ℝ)^4 * Real.pi^2 * (Real.exp (9*t)*9)
        - 9375 * (n : ℝ)^2 * Real.pi^1 * (Real.exp (5*t)*5)) t := by
    convert
      (((((((h29.const_mul (-2048 * (n : ℝ)^14 * Real.pi^7)).add
        (h25.const_mul (46592 * (n : ℝ)^12 * Real.pi^6))).add
        (h21.const_mul (-343040 * (n : ℝ)^10 * Real.pi^5))).add
        (h17.const_mul (976320 * (n : ℝ)^8 * Real.pi^4))).add
        (h13.const_mul (-1008968 * (n : ℝ)^6 * Real.pi^3))).add
        (h9.const_mul (285870 * (n : ℝ)^4 * Real.pi^2))).add
        (h5.const_mul (-9375 * (n : ℝ)^2 * Real.pi^1)))
      using 1
    all_goals
      first
      | funext s; ring
      | ring
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
  have h33exp : Real.exp (33*t) =
      Real.exp (29*t)*Real.exp (4*t) := by
    rw [show (33:ℝ)*t = 29*t + 4*t by ring, Real.exp_add]
  have h29exp : Real.exp (29*t) =
      Real.exp (25*t)*Real.exp (4*t) := by
    rw [show (29:ℝ)*t = 25*t + 4*t by ring, Real.exp_add]
  have h25exp : Real.exp (25*t) =
      Real.exp (21*t)*Real.exp (4*t) := by
    rw [show (25:ℝ)*t = 21*t + 4*t by ring, Real.exp_add]
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
    simp only [phiSummandFifthDerivative, Pi.mul_apply]
    ring
  · simp only [phiSummandSixthDerivative]
    rw [h33exp, h29exp, h25exp, h21exp, h17exp, h13exp, h9exp]
    ring

theorem phiSummandSixthDerivative_summable (t : ℝ) :
    Summable (fun n : ℕ => phiSummandSixthDerivative n t) := by
  let a : ℝ := Real.pi * Real.exp (4*t)
  have ha : 0 < a := mul_pos Real.pi_pos (Real.exp_pos _)
  have h16 : Summable (fun n : ℕ =>
      (n : ℝ)^16 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 16 a ha
  have h14 : Summable (fun n : ℕ =>
      (n : ℝ)^14 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 14 a ha
  have h12 : Summable (fun n : ℕ =>
      (n : ℝ)^12 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 12 a ha
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
    ((((((((h16.mul_left (8192 * Real.pi^8 * Real.exp (33*t))).add
      (h14.mul_left (-245760 * Real.pi^7 * Real.exp (29*t)))).add
      (h12.mul_left (2536960 * Real.pi^6 * Real.exp (25*t)))).add
      (h10.mul_left (-11109120 * Real.pi^5 * Real.exp (21*t)))).add
      (h8.mul_left (20633312 * Real.pi^4 * Real.exp (17*t)))).add
      (h6.mul_left (-14260064 * Real.pi^3 * Real.exp (13*t)))).add
      (h4.mul_left (2610330 * Real.pi^2 * Real.exp (9*t)))).add
      (h2.mul_left (-46875 * Real.pi^1 * Real.exp (5*t))))
  convert hs using 1
  funext n
  simp only [phiSummandSixthDerivative]
  have heq : -a * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*t) := by
    dsimp [a]
    ring
  rw [heq]
  ring

noncomputable def phiSixthDerivativeEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  (8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b)
         + 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a))

theorem phiSixthDerivativeEnvelope_summable (a b : ℝ) :
    Summable (phiSixthDerivativeEnvelope a b) := by
  let q : ℝ := Real.pi * Real.exp (4*a)
  have hq : 0 < q := mul_pos Real.pi_pos (Real.exp_pos _)
  have h16 : Summable (fun n : ℕ =>
      (n : ℝ)^16 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 16 q hq
  have h14 : Summable (fun n : ℕ =>
      (n : ℝ)^14 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 14 q hq
  have h12 : Summable (fun n : ℕ =>
      (n : ℝ)^12 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 12 q hq
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
    ((((((((h16.mul_left (8192 * Real.pi^8 * Real.exp (33*b))).add
      (h14.mul_left (245760 * Real.pi^7 * Real.exp (29*b)))).add
      (h12.mul_left (2536960 * Real.pi^6 * Real.exp (25*b)))).add
      (h10.mul_left (11109120 * Real.pi^5 * Real.exp (21*b)))).add
      (h8.mul_left (20633312 * Real.pi^4 * Real.exp (17*b)))).add
      (h6.mul_left (14260064 * Real.pi^3 * Real.exp (13*b)))).add
      (h4.mul_left (2610330 * Real.pi^2 * Real.exp (9*b)))).add
      (h2.mul_left (46875 * Real.pi^1 * Real.exp (5*b))))
  convert hs using 1
  funext n
  dsimp [phiSixthDerivativeEnvelope, q]
  rw [show -(Real.pi * Real.exp (4*a)) * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*a) by ring]
  ring

theorem phiSummandSixthDerivative_le_envelope
    (a b x : ℝ) (n : ℕ)
    (hax : a ≤ x) (hxb : x ≤ b) :
    ‖phiSummandSixthDerivative n x‖ ≤
      phiSixthDerivativeEnvelope a b n := by
  have h4 : Real.exp (4*a) ≤ Real.exp (4*x) :=
    Real.exp_le_exp.mpr (by linarith)
  have h33 : Real.exp (33*x) ≤ Real.exp (33*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h29 : Real.exp (29*x) ≤ Real.exp (29*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h25 : Real.exp (25*x) ≤ Real.exp (25*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h21 : Real.exp (21*x) ≤ Real.exp (21*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h17 : Real.exp (17*x) ≤ Real.exp (17*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h13 : Real.exp (13*x) ≤ Real.exp (13*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9 : Real.exp (9*x) ≤ Real.exp (9*b) :=
    Real.exp_le_exp.mpr (by linarith)
  have h5 : Real.exp (5*x) ≤ Real.exp (5*b) :=
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
  have h33' :
      8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x) ≤
      8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b) :=
    mul_le_mul_of_nonneg_left h33 (by positivity)
  have h29' :
      245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x) ≤
      245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b) :=
    mul_le_mul_of_nonneg_left h29 (by positivity)
  have h25' :
      2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x) ≤
      2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b) :=
    mul_le_mul_of_nonneg_left h25 (by positivity)
  have h21' :
      11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) ≤
      11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b) :=
    mul_le_mul_of_nonneg_left h21 (by positivity)
  have h17' :
      20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) ≤
      20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) :=
    mul_le_mul_of_nonneg_left h17 (by positivity)
  have h13' :
      14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) ≤
      14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) :=
    mul_le_mul_of_nonneg_left h13 (by positivity)
  have h9' :
      2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) ≤
      2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) :=
    mul_le_mul_of_nonneg_left h9 (by positivity)
  have h5' :
      46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) ≤
      46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have hpoly :
      8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
         + 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) ≤
      8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b)
         + 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) := by
    linarith
  have hn8 :
      0 ≤ 8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x) := by positivity
  have hn7 :
      0 ≤ 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x) := by positivity
  have hn6 :
      0 ≤ 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x) := by positivity
  have hn5 :
      0 ≤ 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) := by positivity
  have hn4 :
      0 ≤ 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) := by positivity
  have hn3 :
      0 ≤ 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) := by positivity
  have hn2 :
      0 ≤ 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) := by positivity
  have hn1 :
      0 ≤ 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) := by positivity
  have habs :
      |(8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
        - 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
        + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
        - 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
        + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
        - 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
        + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
        - 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x))| ≤
      8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
         + 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnonneg :
      0 ≤ 8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b)
         + 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) := by
    positivity
  calc
    ‖phiSummandSixthDerivative n x‖ =
        |(8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
        - 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
        + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
        - 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
        + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
        - 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
        + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
        - 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x))| *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) := by
          simp only [Real.norm_eq_abs, phiSummandSixthDerivative,
            abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
         + 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) :=
          mul_le_mul_of_nonneg_right habs (le_of_lt (Real.exp_pos _))
    _ ≤ (8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b)
         + 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a)) := by
          exact mul_le_mul hpoly hdecay
            (le_of_lt (Real.exp_pos _)) hnonneg
    _ = phiSixthDerivativeEnvelope a b n := rfl

theorem Phi_fifth_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 5 Phi)
      (∑' n : ℕ, phiSummandSixthDerivative n t) t := by
  have ht : t ∈ Set.Ioo (t-1) (t+1) := by
    constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (phiSixthDerivativeEnvelope_summable (t-1) (t+1))
    isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => phiSummandFifthDerivative_hasDerivAt n s)
    (fun n s hs => phiSummandSixthDerivative_le_envelope
      (t-1) (t+1) s n hs.1.le hs.2.le)
    ht (phiSummandFifthDerivative_summable t) ht
  have hfun :
      (fun s : ℝ => ∑' n : ℕ, phiSummandFifthDerivative n s) =
        iteratedDeriv 5 Phi := by
    funext s
    exact (Phi_fifthDerivative s).symm
  rw [hfun] at h
  exact h

theorem Phi_sixthDerivative (t : ℝ) :
    iteratedDeriv 6 Phi t =
      ∑' n : ℕ, phiSummandSixthDerivative n t := by
  rw [show (6:ℕ) = 5+1 by omega, iteratedDeriv_succ]
  exact (Phi_fifth_hasDerivAt t).deriv

theorem Phi_fifth_differentiable :
    Differentiable ℝ (iteratedDeriv 5 Phi) := by
  intro t
  exact (Phi_fifth_hasDerivAt t).differentiableAt

theorem Psi1_sixth_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 6 Psi1)
      (-(∑' n : ℕ, phiSummandSixthDerivative n t)) t := by
  have hprev : iteratedDeriv 6 Psi1 =
      fun s : ℝ => -(iteratedDeriv 5 Phi s) := by
    funext s
    rw [Psi1_sixth_derivative, Phi_fifthDerivative]
  rw [hprev]
  exact (Phi_fifth_hasDerivAt t).neg

theorem Psi1_seventh_derivative (t : ℝ) :
    iteratedDeriv 7 Psi1 t =
      -(∑' n : ℕ, phiSummandSixthDerivative n t) := by
  rw [show (7:ℕ) = 6+1 by omega, iteratedDeriv_succ]
  exact (Psi1_sixth_hasDerivAt t).deriv

theorem Psi1_sixth_differentiable :
    Differentiable ℝ (iteratedDeriv 6 Psi1) := by
  intro t
  exact (Psi1_sixth_hasDerivAt t).differentiableAt

end W5
