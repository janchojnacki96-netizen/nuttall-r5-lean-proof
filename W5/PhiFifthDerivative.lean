import W5.PhiFourthDerivative
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Original theta series: derivative order 5

This proof is about the actual Riemann theta series, not a surrogate.
It uses an explicit Gaussian-polynomial summable envelope on compact
intervals to justify differentiation under the infinite sum.
Nothing here asserts an order-5 Wronskian sign.
-/

namespace W5

noncomputable def phiSummandFifthDerivative (n : ℕ) (t : ℝ) : ℝ :=
  (-2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*t)
        + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*t)
        - 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*t)
        + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*t)
        - 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*t)
        + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*t)
        - 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*t)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))

theorem phiSummandFourthDerivative_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (phiSummandFourthDerivative n)
      (phiSummandFifthDerivative n t) t := by
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
        512 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*s)
        - 8448 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*s)
        + 41408 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*s)
        - 68096 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*s)
        + 30930 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*s)
        - 1875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*s))
      (512 * (n : ℝ)^12 * Real.pi^6 * (Real.exp (25*t)*25)
        - 8448 * (n : ℝ)^10 * Real.pi^5 * (Real.exp (21*t)*21)
        + 41408 * (n : ℝ)^8 * Real.pi^4 * (Real.exp (17*t)*17)
        - 68096 * (n : ℝ)^6 * Real.pi^3 * (Real.exp (13*t)*13)
        + 30930 * (n : ℝ)^4 * Real.pi^2 * (Real.exp (9*t)*9)
        - 1875 * (n : ℝ)^2 * Real.pi^1 * (Real.exp (5*t)*5)) t := by
    convert
      ((((((h25.const_mul (512 * (n : ℝ)^12 * Real.pi^6)).add
        (h21.const_mul (-8448 * (n : ℝ)^10 * Real.pi^5))).add
        (h17.const_mul (41408 * (n : ℝ)^8 * Real.pi^4))).add
        (h13.const_mul (-68096 * (n : ℝ)^6 * Real.pi^3))).add
        (h9.const_mul (30930 * (n : ℝ)^4 * Real.pi^2))).add
        (h5.const_mul (-1875 * (n : ℝ)^2 * Real.pi^1)))
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
    simp only [phiSummandFourthDerivative, Pi.mul_apply]
    ring
  · simp only [phiSummandFifthDerivative]
    rw [h29exp, h25exp, h21exp, h17exp, h13exp, h9exp]
    ring

theorem phiSummandFifthDerivative_summable (t : ℝ) :
    Summable (fun n : ℕ => phiSummandFifthDerivative n t) := by
  let a : ℝ := Real.pi * Real.exp (4*t)
  have ha : 0 < a := mul_pos Real.pi_pos (Real.exp_pos _)
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
    (((((((h14.mul_left (-2048 * Real.pi^7 * Real.exp (29*t))).add
      (h12.mul_left (46592 * Real.pi^6 * Real.exp (25*t)))).add
      (h10.mul_left (-343040 * Real.pi^5 * Real.exp (21*t)))).add
      (h8.mul_left (976320 * Real.pi^4 * Real.exp (17*t)))).add
      (h6.mul_left (-1008968 * Real.pi^3 * Real.exp (13*t)))).add
      (h4.mul_left (285870 * Real.pi^2 * Real.exp (9*t)))).add
      (h2.mul_left (-9375 * Real.pi^1 * Real.exp (5*t))))
  convert hs using 1
  funext n
  simp only [phiSummandFifthDerivative]
  have heq : -a * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*t) := by
    dsimp [a]
    ring
  rw [heq]
  ring

noncomputable def phiFifthDerivativeEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  (2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a))

theorem phiFifthDerivativeEnvelope_summable (a b : ℝ) :
    Summable (phiFifthDerivativeEnvelope a b) := by
  let q : ℝ := Real.pi * Real.exp (4*a)
  have hq : 0 < q := mul_pos Real.pi_pos (Real.exp_pos _)
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
    (((((((h14.mul_left (2048 * Real.pi^7 * Real.exp (29*b))).add
      (h12.mul_left (46592 * Real.pi^6 * Real.exp (25*b)))).add
      (h10.mul_left (343040 * Real.pi^5 * Real.exp (21*b)))).add
      (h8.mul_left (976320 * Real.pi^4 * Real.exp (17*b)))).add
      (h6.mul_left (1008968 * Real.pi^3 * Real.exp (13*b)))).add
      (h4.mul_left (285870 * Real.pi^2 * Real.exp (9*b)))).add
      (h2.mul_left (9375 * Real.pi^1 * Real.exp (5*b))))
  convert hs using 1
  funext n
  dsimp [phiFifthDerivativeEnvelope, q]
  rw [show -(Real.pi * Real.exp (4*a)) * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*a) by ring]
  ring

theorem phiSummandFifthDerivative_le_envelope
    (a b x : ℝ) (n : ℕ)
    (hax : a ≤ x) (hxb : x ≤ b) :
    ‖phiSummandFifthDerivative n x‖ ≤
      phiFifthDerivativeEnvelope a b n := by
  have h4 : Real.exp (4*a) ≤ Real.exp (4*x) :=
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
  have h29' :
      2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x) ≤
      2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b) :=
    mul_le_mul_of_nonneg_left h29 (by positivity)
  have h25' :
      46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x) ≤
      46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b) :=
    mul_le_mul_of_nonneg_left h25 (by positivity)
  have h21' :
      343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) ≤
      343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b) :=
    mul_le_mul_of_nonneg_left h21 (by positivity)
  have h17' :
      976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) ≤
      976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) :=
    mul_le_mul_of_nonneg_left h17 (by positivity)
  have h13' :
      1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) ≤
      1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) :=
    mul_le_mul_of_nonneg_left h13 (by positivity)
  have h9' :
      285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) ≤
      285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) :=
    mul_le_mul_of_nonneg_left h9 (by positivity)
  have h5' :
      9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) ≤
      9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have hpoly :
      2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) ≤
      2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) := by
    linarith
  have hn7 :
      0 ≤ 2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x) := by positivity
  have hn6 :
      0 ≤ 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x) := by positivity
  have hn5 :
      0 ≤ 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) := by positivity
  have hn4 :
      0 ≤ 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) := by positivity
  have hn3 :
      0 ≤ 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) := by positivity
  have hn2 :
      0 ≤ 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) := by positivity
  have hn1 :
      0 ≤ 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) := by positivity
  have habs :
      |(-2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
        + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
        - 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
        + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
        - 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
        + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
        - 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x))| ≤
      2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnonneg :
      0 ≤ 2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) := by
    positivity
  calc
    ‖phiSummandFifthDerivative n x‖ =
        |(-2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
        + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
        - 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
        + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
        - 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
        + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
        - 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x))| *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) := by
          simp only [Real.norm_eq_abs, phiSummandFifthDerivative,
            abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) :=
          mul_le_mul_of_nonneg_right habs (le_of_lt (Real.exp_pos _))
    _ ≤ (2048 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 46592 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 343040 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 976320 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 1008968 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 285870 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 9375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a)) := by
          exact mul_le_mul hpoly hdecay
            (le_of_lt (Real.exp_pos _)) hnonneg
    _ = phiFifthDerivativeEnvelope a b n := rfl

theorem Phi_fourth_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 4 Phi)
      (∑' n : ℕ, phiSummandFifthDerivative n t) t := by
  have ht : t ∈ Set.Ioo (t-1) (t+1) := by
    constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (phiFifthDerivativeEnvelope_summable (t-1) (t+1))
    isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => phiSummandFourthDerivative_hasDerivAt n s)
    (fun n s hs => phiSummandFifthDerivative_le_envelope
      (t-1) (t+1) s n hs.1.le hs.2.le)
    ht (phiSummandFourthDerivative_summable t) ht
  have hfun :
      (fun s : ℝ => ∑' n : ℕ, phiSummandFourthDerivative n s) =
        iteratedDeriv 4 Phi := by
    funext s
    exact (Phi_fourthDerivative s).symm
  rw [hfun] at h
  exact h

theorem Phi_fifthDerivative (t : ℝ) :
    iteratedDeriv 5 Phi t =
      ∑' n : ℕ, phiSummandFifthDerivative n t := by
  rw [show (5:ℕ) = 4+1 by omega, iteratedDeriv_succ]
  exact (Phi_fourth_hasDerivAt t).deriv

theorem Phi_fourth_differentiable :
    Differentiable ℝ (iteratedDeriv 4 Phi) := by
  intro t
  exact (Phi_fourth_hasDerivAt t).differentiableAt

theorem Psi1_fifth_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 5 Psi1)
      (-(∑' n : ℕ, phiSummandFifthDerivative n t)) t := by
  have hprev : iteratedDeriv 5 Psi1 =
      fun s : ℝ => -(iteratedDeriv 4 Phi s) := by
    funext s
    rw [Psi1_fifth_derivative, Phi_fourthDerivative]
  rw [hprev]
  exact (Phi_fourth_hasDerivAt t).neg

theorem Psi1_sixth_derivative (t : ℝ) :
    iteratedDeriv 6 Psi1 t =
      -(∑' n : ℕ, phiSummandFifthDerivative n t) := by
  rw [show (6:ℕ) = 5+1 by omega, iteratedDeriv_succ]
  exact (Psi1_fifth_hasDerivAt t).deriv

theorem Psi1_fifth_differentiable :
    Differentiable ℝ (iteratedDeriv 5 Psi1) := by
  intro t
  exact (Psi1_fifth_hasDerivAt t).differentiableAt

end W5
