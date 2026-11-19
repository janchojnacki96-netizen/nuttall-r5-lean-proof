import W5.PhiSixthDerivative
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Original theta series: derivative order 7

This proof is about the actual Riemann theta series, not a surrogate.
It uses an explicit Gaussian-polynomial summable envelope on compact
intervals to justify differentiation under the infinite sum.
Nothing here asserts an order-7 Wronskian sign.
-/

namespace W5

noncomputable def phiSummandSeventhDerivative (n : ℕ) (t : ℝ) : ℝ :=
  (-32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*t)
        + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*t)
        - 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*t)
        + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*t)
        - 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*t)
        + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*t)
        - 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*t)
        + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*t)
        - 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*t)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))

theorem phiSummandSixthDerivative_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (phiSummandSixthDerivative n)
      (phiSummandSeventhDerivative n t) t := by
  have hlin33 : HasDerivAt (fun s : ℝ => (33:ℝ)*s) 33 t := by
    simpa using (hasDerivAt_id t).const_mul (33:ℝ)
  have h33 : HasDerivAt (fun s : ℝ => Real.exp (33*s))
      (Real.exp (33*t)*33) t :=
    (Real.hasDerivAt_exp (33*t)).comp t hlin33
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
        8192 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*s)
        - 245760 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*s)
        + 2536960 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*s)
        - 11109120 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*s)
        + 20633312 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*s)
        - 14260064 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*s)
        + 2610330 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*s)
        - 46875 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*s))
      (8192 * (n : ℝ)^16 * Real.pi^8 * (Real.exp (33*t)*33)
        - 245760 * (n : ℝ)^14 * Real.pi^7 * (Real.exp (29*t)*29)
        + 2536960 * (n : ℝ)^12 * Real.pi^6 * (Real.exp (25*t)*25)
        - 11109120 * (n : ℝ)^10 * Real.pi^5 * (Real.exp (21*t)*21)
        + 20633312 * (n : ℝ)^8 * Real.pi^4 * (Real.exp (17*t)*17)
        - 14260064 * (n : ℝ)^6 * Real.pi^3 * (Real.exp (13*t)*13)
        + 2610330 * (n : ℝ)^4 * Real.pi^2 * (Real.exp (9*t)*9)
        - 46875 * (n : ℝ)^2 * Real.pi^1 * (Real.exp (5*t)*5)) t := by
    convert
      ((((((((h33.const_mul (8192 * (n : ℝ)^16 * Real.pi^8)).add
        (h29.const_mul (-245760 * (n : ℝ)^14 * Real.pi^7))).add
        (h25.const_mul (2536960 * (n : ℝ)^12 * Real.pi^6))).add
        (h21.const_mul (-11109120 * (n : ℝ)^10 * Real.pi^5))).add
        (h17.const_mul (20633312 * (n : ℝ)^8 * Real.pi^4))).add
        (h13.const_mul (-14260064 * (n : ℝ)^6 * Real.pi^3))).add
        (h9.const_mul (2610330 * (n : ℝ)^4 * Real.pi^2))).add
        (h5.const_mul (-46875 * (n : ℝ)^2 * Real.pi^1)))
      using 1
    all_goals
      first
      | funext s
        simp only [Pi.add_apply]
        ring_nf
      | ring_nf
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
  have h37exp : Real.exp (37*t) =
      Real.exp (33*t)*Real.exp (4*t) := by
    rw [show (37:ℝ)*t = 33*t + 4*t by ring, Real.exp_add]
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
    simp only [phiSummandSixthDerivative, Pi.mul_apply]
    ring_nf
  · simp only [phiSummandSeventhDerivative]
    rw [h37exp, h33exp, h29exp, h25exp, h21exp, h17exp, h13exp, h9exp] <;> ring

theorem phiSummandSeventhDerivative_summable (t : ℝ) :
    Summable (fun n : ℕ => phiSummandSeventhDerivative n t) := by
  let a : ℝ := Real.pi * Real.exp (4*t)
  have ha : 0 < a := mul_pos Real.pi_pos (Real.exp_pos _)
  have h18 : Summable (fun n : ℕ =>
      (n : ℝ)^18 * Real.exp (-a * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 18 a ha
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
    (((((((((h18.mul_left (-32768 * Real.pi^9 * Real.exp (37*t))).add
      (h16.mul_left (1253376 * Real.pi^8 * Real.exp (33*t)))).add
      (h14.mul_left (-17274880 * Real.pi^7 * Real.exp (29*t)))).add
      (h12.mul_left (107860480 * Real.pi^6 * Real.exp (25*t)))).add
      (h10.mul_left (-315824768 * Real.pi^5 * Real.exp (21*t)))).add
      (h8.mul_left (407806560 * Real.pi^4 * Real.exp (17*t)))).add
      (h6.mul_left (-195822152 * Real.pi^3 * Real.exp (13*t)))).add
      (h4.mul_left (23680470 * Real.pi^2 * Real.exp (9*t)))).add
      (h2.mul_left (-234375 * Real.pi^1 * Real.exp (5*t))))
  convert hs using 1
  funext n
  simp only [phiSummandSeventhDerivative]
  have heq : -a * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*t) := by
    dsimp [a]
    ring
  rw [heq]
  ring

noncomputable def phiSeventhDerivativeEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  (32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*b)
         + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b)
         + 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b)) *
      Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a))

theorem phiSeventhDerivativeEnvelope_summable (a b : ℝ) :
    Summable (phiSeventhDerivativeEnvelope a b) := by
  let q : ℝ := Real.pi * Real.exp (4*a)
  have hq : 0 < q := mul_pos Real.pi_pos (Real.exp_pos _)
  have h18 : Summable (fun n : ℕ =>
      (n : ℝ)^18 * Real.exp (-q * (n : ℝ)^2)) :=
    theta_gaussian_polynomial_summable 18 q hq
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
    (((((((((h18.mul_left (32768 * Real.pi^9 * Real.exp (37*b))).add
      (h16.mul_left (1253376 * Real.pi^8 * Real.exp (33*b)))).add
      (h14.mul_left (17274880 * Real.pi^7 * Real.exp (29*b)))).add
      (h12.mul_left (107860480 * Real.pi^6 * Real.exp (25*b)))).add
      (h10.mul_left (315824768 * Real.pi^5 * Real.exp (21*b)))).add
      (h8.mul_left (407806560 * Real.pi^4 * Real.exp (17*b)))).add
      (h6.mul_left (195822152 * Real.pi^3 * Real.exp (13*b)))).add
      (h4.mul_left (23680470 * Real.pi^2 * Real.exp (9*b)))).add
      (h2.mul_left (234375 * Real.pi^1 * Real.exp (5*b))))
  convert hs using 1
  funext n
  dsimp [phiSeventhDerivativeEnvelope, q]
  rw [show -(Real.pi * Real.exp (4*a)) * (n : ℝ)^2 =
      -(n : ℝ)^2 * Real.pi * Real.exp (4*a) by ring]
  ring

theorem phiSummandSeventhDerivative_le_envelope
    (a b x : ℝ) (n : ℕ)
    (hax : a ≤ x) (hxb : x ≤ b) :
    ‖phiSummandSeventhDerivative n x‖ ≤
      phiSeventhDerivativeEnvelope a b n := by
  have h4 : Real.exp (4*a) ≤ Real.exp (4*x) :=
    Real.exp_le_exp.mpr (by linarith)
  have h37 : Real.exp (37*x) ≤ Real.exp (37*b) :=
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
  have h37' :
      32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*x) ≤
      32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*b) :=
    mul_le_mul_of_nonneg_left h37 (by positivity)
  have h33' :
      1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x) ≤
      1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b) :=
    mul_le_mul_of_nonneg_left h33 (by positivity)
  have h29' :
      17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x) ≤
      17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b) :=
    mul_le_mul_of_nonneg_left h29 (by positivity)
  have h25' :
      107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x) ≤
      107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b) :=
    mul_le_mul_of_nonneg_left h25 (by positivity)
  have h21' :
      315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) ≤
      315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b) :=
    mul_le_mul_of_nonneg_left h21 (by positivity)
  have h17' :
      407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) ≤
      407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b) :=
    mul_le_mul_of_nonneg_left h17 (by positivity)
  have h13' :
      195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) ≤
      195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b) :=
    mul_le_mul_of_nonneg_left h13 (by positivity)
  have h9' :
      23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) ≤
      23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b) :=
    mul_le_mul_of_nonneg_left h9 (by positivity)
  have h5' :
      234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) ≤
      234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have hpoly :
      32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*x)
         + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
         + 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) ≤
      32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*b)
         + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b)
         + 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) := by
    linarith
  have hn9 :
      0 ≤ 32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*x) := by positivity
  have hn8 :
      0 ≤ 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x) := by positivity
  have hn7 :
      0 ≤ 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x) := by positivity
  have hn6 :
      0 ≤ 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x) := by positivity
  have hn5 :
      0 ≤ 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x) := by positivity
  have hn4 :
      0 ≤ 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x) := by positivity
  have hn3 :
      0 ≤ 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x) := by positivity
  have hn2 :
      0 ≤ 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x) := by positivity
  have hn1 :
      0 ≤ 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) := by positivity
  have habs :
      |(-32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*x)
        + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
        - 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
        + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
        - 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
        + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
        - 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
        + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
        - 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x))| ≤
      32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*x)
         + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
         + 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnonneg :
      0 ≤ 32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*b)
         + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b)
         + 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b) := by
    positivity
  calc
    ‖phiSummandSeventhDerivative n x‖ =
        |(-32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*x)
        + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
        - 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
        + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
        - 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
        + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
        - 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
        + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
        - 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x))| *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) := by
          simp only [Real.norm_eq_abs, phiSummandSeventhDerivative,
            abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*x)
         + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*x)
         + 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*x)
         + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*x)
         + 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*x)
         + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*x)
         + 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*x)
         + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*x)
         + 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*x)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*x)) :=
          mul_le_mul_of_nonneg_right habs (le_of_lt (Real.exp_pos _))
    _ ≤ (32768 * (n : ℝ)^18 * Real.pi^9 * Real.exp (37*b)
         + 1253376 * (n : ℝ)^16 * Real.pi^8 * Real.exp (33*b)
         + 17274880 * (n : ℝ)^14 * Real.pi^7 * Real.exp (29*b)
         + 107860480 * (n : ℝ)^12 * Real.pi^6 * Real.exp (25*b)
         + 315824768 * (n : ℝ)^10 * Real.pi^5 * Real.exp (21*b)
         + 407806560 * (n : ℝ)^8 * Real.pi^4 * Real.exp (17*b)
         + 195822152 * (n : ℝ)^6 * Real.pi^3 * Real.exp (13*b)
         + 23680470 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)
         + 234375 * (n : ℝ)^2 * Real.pi^1 * Real.exp (5*b)) *
        Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a)) := by
          exact mul_le_mul hpoly hdecay
            (le_of_lt (Real.exp_pos _)) hnonneg
    _ = phiSeventhDerivativeEnvelope a b n := rfl

theorem Phi_sixth_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 6 Phi)
      (∑' n : ℕ, phiSummandSeventhDerivative n t) t := by
  have ht : t ∈ Set.Ioo (t-1) (t+1) := by
    constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (phiSeventhDerivativeEnvelope_summable (t-1) (t+1))
    isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => phiSummandSixthDerivative_hasDerivAt n s)
    (fun n s hs => phiSummandSeventhDerivative_le_envelope
      (t-1) (t+1) s n hs.1.le hs.2.le)
    ht (phiSummandSixthDerivative_summable t) ht
  have hfun :
      (fun s : ℝ => ∑' n : ℕ, phiSummandSixthDerivative n s) =
        iteratedDeriv 6 Phi := by
    funext s
    exact (Phi_sixthDerivative s).symm
  rw [hfun] at h
  exact h

theorem Phi_seventhDerivative (t : ℝ) :
    iteratedDeriv 7 Phi t =
      ∑' n : ℕ, phiSummandSeventhDerivative n t := by
  rw [show (7:ℕ) = 6+1 by omega, iteratedDeriv_succ]
  exact (Phi_sixth_hasDerivAt t).deriv

theorem Phi_sixth_differentiable :
    Differentiable ℝ (iteratedDeriv 6 Phi) := by
  intro t
  exact (Phi_sixth_hasDerivAt t).differentiableAt

theorem Psi1_seventh_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 7 Psi1)
      (-(∑' n : ℕ, phiSummandSeventhDerivative n t)) t := by
  have hprev : iteratedDeriv 7 Psi1 =
      fun s : ℝ => -(iteratedDeriv 6 Phi s) := by
    funext s
    rw [Psi1_seventh_derivative, Phi_sixthDerivative]
  rw [hprev]
  exact (Phi_sixth_hasDerivAt t).neg

theorem Psi1_eighth_derivative (t : ℝ) :
    iteratedDeriv 8 Psi1 t =
      -(∑' n : ℕ, phiSummandSeventhDerivative n t) := by
  rw [show (8:ℕ) = 7+1 by omega, iteratedDeriv_succ]
  exact (Psi1_seventh_hasDerivAt t).deriv

theorem Psi1_seventh_differentiable :
    Differentiable ℝ (iteratedDeriv 7 Psi1) := by
  intro t
  exact (Psi1_seventh_hasDerivAt t).differentiableAt

end W5
