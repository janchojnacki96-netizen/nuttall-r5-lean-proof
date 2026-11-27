import W5.ThetaPhiSummability
import Mathlib.Analysis.Calculus.SmoothSeries

namespace Nuttall

/-- The summand of the auxiliary series in the Andréief integral (Section 4). -/
noncomputable def auxiliarySummand (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ)^2 * Real.pi * Real.exp (5*t)) *
    Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))

theorem auxiliarySummand_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (auxiliarySummand n)
      (-2 * W5.phiSummand n t - auxiliarySummand n t) t := by
  have hlin (a : ℝ) : HasDerivAt (fun s : ℝ => a*s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have h5 := (Real.hasDerivAt_exp (5*t)).comp t (hlin 5)
  have h4 := (Real.hasDerivAt_exp (4*t)).comp t (hlin 4)
  have harg := h4.const_mul (-(n : ℝ)^2 * Real.pi)
  have hdecay := (Real.hasDerivAt_exp _).comp t harg
  have h := (h5.const_mul ((n : ℝ)^2 * Real.pi)).mul hdecay
  convert h using 1
  · rfl
  · simp only [auxiliarySummand, W5.phiSummand, Function.comp_apply]
    rw [show (9:ℝ)*t = 5*t + 4*t by ring, Real.exp_add]
    ring

theorem twice_phiSummand_eq_neg_deriv_add (n : ℕ) (t : ℝ) :
    2 * W5.phiSummand n t =
      -(deriv (auxiliarySummand n) t + auxiliarySummand n t) := by
  rw [(auxiliarySummand_hasDerivAt n t).deriv]
  ring

/-- The auxiliary function g from Section 4. -/
noncomputable def auxiliaryTheta (t : ℝ) : ℝ :=
  ∑' n : ℕ, auxiliarySummand n t

theorem auxiliarySummand_summable (t : ℝ) :
    Summable (fun n : ℕ => auxiliarySummand n t) := by
  let q := Real.pi * Real.exp (4*t)
  have hq : 0 < q := by dsimp [q]; positivity
  convert (W5.theta_gaussian_polynomial_summable 2 q hq).mul_left
      (Real.pi * Real.exp (5*t)) using 1
  funext n
  unfold auxiliarySummand
  rw [show -q * (n : ℝ)^2 = -(n : ℝ)^2 * Real.pi * Real.exp (4*t) by
    dsimp [q]
    ring]
  ring

private noncomputable def auxiliaryDerivativeEnvelope (a b : ℝ) (n : ℕ) : ℝ :=
  (4 * ((n : ℝ)^4 * Real.pi^2 * Real.exp (9*b)) +
    5 * ((n : ℝ)^2 * Real.pi * Real.exp (5*b))) *
    Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*a))

private theorem auxiliaryDerivativeEnvelope_summable (a b : ℝ) :
    Summable (auxiliaryDerivativeEnvelope a b) := by
  let q := Real.pi * Real.exp (4*a)
  have hq : 0 < q := by dsimp [q]; positivity
  have h :=
    ((W5.theta_gaussian_polynomial_summable 4 q hq).mul_left
      (4 * Real.pi^2 * Real.exp (9*b))).add
    ((W5.theta_gaussian_polynomial_summable 2 q hq).mul_left
      (5 * Real.pi * Real.exp (5*b)))
  convert h using 1
  funext n
  unfold auxiliaryDerivativeEnvelope
  rw [show -q * (n : ℝ)^2 = -(n : ℝ)^2 * Real.pi * Real.exp (4*a) by
    dsimp [q]
    ring]
  ring

private theorem auxiliaryDerivative_le_envelope (a b t : ℝ) (n : ℕ)
    (ha : a ≤ t) (hb : t ≤ b) :
    ‖-2 * W5.phiSummand n t - auxiliarySummand n t‖ ≤
      auxiliaryDerivativeEnvelope a b n := by
  let A := fun s : ℝ => (n : ℝ)^4 * Real.pi^2 * Real.exp (9*s)
  let B := fun s : ℝ => (n : ℝ)^2 * Real.pi * Real.exp (5*s)
  let E := fun s : ℝ => Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*s))
  change ‖-2 * ((2*A t - 3*B t) * E t) - B t * E t‖ ≤
    (4*A b + 5*B b) * E a
  have hpoly : 4*A t + 5*B t ≤ 4*A b + 5*B b := by
    have hA : A t ≤ A b := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    have hB : B t ≤ B b := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    linarith
  have hE : E t ≤ E a := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (Real.exp_le_exp.mpr (by linarith))
      (by have hp : 0 ≤ (n : ℝ)^2 * Real.pi := by positivity
          convert neg_nonpos.mpr hp using 1 <;> ring)
  have hEt : 0 ≤ E t := (Real.exp_pos _).le
  have hAt : 0 ≤ A t := by dsimp [A]; positivity
  have hBt : 0 ≤ B t := by dsimp [B]; positivity
  have habs : |5*B t - 4*A t| ≤ 4*A t + 5*B t := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [show -2 * ((2*A t - 3*B t) * E t) - B t * E t =
    (5*B t - 4*A t) * E t by ring, Real.norm_eq_abs, abs_mul, abs_of_nonneg hEt]
  exact mul_le_mul (habs.trans hpoly) hE hEt
    (by dsimp [A, B]; positivity)

theorem auxiliaryTheta_hasDerivAt (t : ℝ) :
    HasDerivAt auxiliaryTheta (-2 * W5.Phi t - auxiliaryTheta t) t := by
  have ht : t ∈ Set.Ioo (t-1) (t+1) := by constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (auxiliaryDerivativeEnvelope_summable (t-1) (t+1))
    isOpen_Ioo isPreconnected_Ioo
    (fun n s _ => auxiliarySummand_hasDerivAt n s)
    (fun n s hs => auxiliaryDerivative_le_envelope
      (t-1) (t+1) s n hs.1.le hs.2.le)
    ht (auxiliarySummand_summable t) ht
  have hs := (W5.phiSummand_summable t).mul_left (-2 : ℝ)
  rw [hs.tsum_sub (auxiliarySummand_summable t), tsum_mul_left,
    ← W5.Phi_eq_tsum_phiSummand] at h
  exact h

theorem twice_phi_eq_neg_deriv_add (t : ℝ) :
    2 * W5.Phi t = -(deriv auxiliaryTheta t + auxiliaryTheta t) := by
  rw [(auxiliaryTheta_hasDerivAt t).deriv]
  ring

#print axioms twice_phi_eq_neg_deriv_add

end Nuttall
