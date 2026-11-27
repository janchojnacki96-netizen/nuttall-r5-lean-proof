import Nuttall.AuxiliaryDerivativePolynomials

namespace Nuttall

open Polynomial
open scoped BigOperators

noncomputable def auxiliaryWeightedSummand (P : ℝ[X]) (n : ℕ) (t : ℝ) : ℝ :=
  auxiliarySummand n t * P.eval (auxiliaryCoordinate n t)

private noncomputable def polynomialExpBound (P : ℝ[X]) : ℝ :=
  ∑ k ∈ P.support, |P.coeff k| * (2^(k+1) * ((k+1).factorial : ℝ))

private theorem polynomialExpBound_nonneg (P : ℝ[X]) : 0 ≤ polynomialExpBound P :=
  Finset.sum_nonneg (fun _ _ => by positivity)

private theorem polynomial_absorption (P : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    x * |P.eval x| ≤ polynomialExpBound P * Real.exp (x/2) := by
  have hpow (k : ℕ) :
      x^(k+1) ≤ (2^(k+1) * ((k+1).factorial : ℝ)) * Real.exp (x/2) := by
    have hf : (0 : ℝ) < ((k+1).factorial : ℝ) := by positivity
    have h := (div_le_iff₀ hf).mp
      (Real.pow_div_factorial_le_exp (x/2) (show 0 ≤ x/2 by positivity) (k+1))
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (2 : ℝ)^(k+1) by positivity)
    rw [div_pow] at hh
    calc
      x^(k+1) = (2 : ℝ)^(k+1) * (x^(k+1) / (2 : ℝ)^(k+1)) := by
        have hn : (2 : ℝ)^(k+1) ≠ 0 := by positivity
        field_simp
      _ ≤ _ := by nlinarith only [hh]
  have habs : |P.eval x| ≤ ∑ k ∈ P.support, |P.coeff k| * x^k := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    simpa only [abs_mul, abs_of_nonneg (pow_nonneg hx _)] using
      (Finset.abs_sum_le_sum_abs (fun k => P.coeff k * x^k) P.support)
  calc
    x * |P.eval x| ≤ x * (∑ k ∈ P.support, |P.coeff k| * x^k) :=
      mul_le_mul_of_nonneg_left habs hx
    _ = ∑ k ∈ P.support, |P.coeff k| * x^(k+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ]
      ring
    _ ≤ ∑ k ∈ P.support, (|P.coeff k| * (2^(k+1) * ((k+1).factorial : ℝ))) *
        Real.exp (x/2) := by
      apply Finset.sum_le_sum
      intro k _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hpow k) (abs_nonneg _)
    _ = _ := by rw [polynomialExpBound, Finset.sum_mul]

private theorem auxiliaryWeightedSummand_le_exp (P : ℝ[X]) (n : ℕ) (t : ℝ) :
    ‖auxiliaryWeightedSummand P n t‖ ≤ polynomialExpBound P *
      Real.exp (t - auxiliaryCoordinate n t / 2) := by
  let x := auxiliaryCoordinate n t
  have hx : 0 ≤ x := by dsimp [x, auxiliaryCoordinate]; positivity
  have hg : auxiliarySummand n t = Real.exp t * x * Real.exp (-x) := by
    unfold auxiliarySummand
    dsimp [x, auxiliaryCoordinate]
    rw [show (5 : ℝ)*t = t + 4*t by ring, Real.exp_add]
    ring
  rw [auxiliaryWeightedSummand, hg, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ Real.exp t * x * Real.exp (-x))]
  calc
    _ = (x * |P.eval x|) * (Real.exp t * Real.exp (-x)) := by ring
    _ ≤ (polynomialExpBound P * Real.exp (x/2)) * (Real.exp t * Real.exp (-x)) :=
      mul_le_mul_of_nonneg_right (polynomial_absorption P hx) (by positivity)
    _ = _ := by
      rw [show t - auxiliaryCoordinate n t / 2 = x/2 + (t + -x) by
        change t - x/2 = _; ring, Real.exp_add, Real.exp_add]
      ring

private theorem gaussianEnvelope_summable {q : ℝ} (hq : 0 < q) :
    Summable (fun n : ℕ => Real.exp (-q * (n : ℝ)^2)) := by
  simpa only [pow_zero, one_mul] using W5.theta_gaussian_polynomial_summable 0 q hq

private noncomputable def localAuxiliaryEnvelope (P : ℝ[X]) (a b : ℝ) (n : ℕ) : ℝ :=
  (polynomialExpBound P * Real.exp b) *
    Real.exp (-(Real.pi * Real.exp (4*a)/2) * (n : ℝ)^2)

private theorem localAuxiliaryEnvelope_summable (P : ℝ[X]) (a b : ℝ) :
    Summable (localAuxiliaryEnvelope P a b) :=
  (gaussianEnvelope_summable (q := Real.pi * Real.exp (4*a)/2) (by positivity)).mul_left _

private theorem auxiliaryWeightedSummand_le_local (P : ℝ[X]) (n : ℕ) {a b t : ℝ}
    (ha : a ≤ t) (hb : t ≤ b) :
    ‖auxiliaryWeightedSummand P n t‖ ≤ localAuxiliaryEnvelope P a b n := by
  have he : Real.exp (4*a) ≤ Real.exp (4*t) := Real.exp_le_exp.mpr (by linarith)
  have hcoord : (n : ℝ)^2 * Real.pi * Real.exp (4*a) ≤ auxiliaryCoordinate n t :=
    mul_le_mul_of_nonneg_left he (by positivity)
  unfold localAuxiliaryEnvelope
  rw [mul_assoc, ← Real.exp_add]
  exact (auxiliaryWeightedSummand_le_exp P n t).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (polynomialExpBound_nonneg P))

theorem auxiliaryWeightedSummand_summable (P : ℝ[X]) (t : ℝ) :
    Summable (fun n => auxiliaryWeightedSummand P n t) :=
  (localAuxiliaryEnvelope_summable P t t).of_norm_bounded
    (fun n => auxiliaryWeightedSummand_le_local P n le_rfl le_rfl)

noncomputable def auxiliarySignedJet (j : ℕ) (t : ℝ) : ℝ :=
  ∑' n, auxiliaryWeightedSummand (auxiliaryDerivativePolynomial j) n t

theorem auxiliarySignedJet_hasDerivAt (j : ℕ) (t : ℝ) :
    HasDerivAt (auxiliarySignedJet j) (-auxiliarySignedJet (j+1) t) t := by
  have ht : t ∈ Set.Ioo (t-1) (t+1) := by constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (localAuxiliaryEnvelope_summable (auxiliaryDerivativePolynomial (j+1)) (t-1) (t+1))
    isOpen_Ioo isPreconnected_Ioo
    (fun n s _ => auxiliary_polynomial_summand_hasDerivAt j n s)
    (fun n s hs => by
      simpa only [norm_neg, auxiliaryWeightedSummand] using
        auxiliaryWeightedSummand_le_local (auxiliaryDerivativePolynomial (j+1)) n hs.1.le hs.2.le)
    ht (auxiliaryWeightedSummand_summable (auxiliaryDerivativePolynomial j) t) ht
  simpa only [auxiliarySignedJet, auxiliaryWeightedSummand, tsum_neg] using h

/-- All real derivatives of the auxiliary theta series, obtained by
termwise differentiation with a locally uniform summable majorant. -/
theorem iteratedDeriv_auxiliaryTheta (j : ℕ) (t : ℝ) :
    iteratedDeriv j auxiliaryTheta t =
      (-1 : ℝ)^j * ∑' n, auxiliaryWeightedSummand (auxiliaryDerivativePolynomial j) n t := by
  change iteratedDeriv j auxiliaryTheta t = (-1 : ℝ)^j * auxiliarySignedJet j t
  induction j generalizing t with
  | zero => simp [auxiliarySignedJet, auxiliaryTheta, auxiliaryWeightedSummand,
      auxiliaryDerivativePolynomial]
  | succ j ih =>
    have hfun : iteratedDeriv j auxiliaryTheta = fun s => (-1 : ℝ)^j * auxiliarySignedJet j s :=
      funext ih
    rw [iteratedDeriv_succ, hfun, ((auxiliarySignedJet_hasDerivAt j t).const_mul ((-1 : ℝ)^j)).deriv,
      pow_succ]
    ring

/-- Uniform exponential decay of each fixed-order signed derivative
summand, with a summable Gaussian factor in the theta index. -/
theorem auxiliaryWeightedSummand_le_exponential (P : ℝ[X]) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖auxiliaryWeightedSummand P n t‖ ≤
      polynomialExpBound P * Real.exp (-(Real.pi/2) * (n : ℝ)^2) * Real.exp (-t) := by
  by_cases hn : n = 0
  · subst n
    simp only [auxiliaryWeightedSummand, auxiliarySummand, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (polynomialExpBound_nonneg P) (Real.exp_nonneg _))
      (Real.exp_nonneg _)
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn2 : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith [sq_nonneg ((n : ℝ)-1)]
  let c := (n : ℝ)^2 * Real.pi
  have hc : 1 ≤ c := by
    have h := mul_le_mul_of_nonneg_right hn2 Real.pi_pos.le
    dsimp [c]
    linarith [Real.pi_gt_three]
  have hcoord : c + 4*t ≤ auxiliaryCoordinate n t := by
    have h1 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (4*t))
      (show 0 ≤ c from le_trans (by norm_num) hc)
    have h2 := mul_le_mul_of_nonneg_right hc (show 0 ≤ 4*t by positivity)
    change c + 4*t ≤ c * Real.exp (4*t)
    nlinarith only [h1, h2]
  rw [mul_assoc, ← Real.exp_add]
  refine (auxiliaryWeightedSummand_le_exp P n t).trans ?_
  apply mul_le_mul_of_nonneg_left _ (polynomialExpBound_nonneg P)
  apply Real.exp_le_exp.mpr
  change t - auxiliaryCoordinate n t / 2 ≤ -(Real.pi/2) * (n : ℝ)^2 + -t
  dsimp [c] at hcoord
  nlinarith only [hcoord]

theorem auxiliaryWeightedSeries_decay (P : ℝ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖∑' n, auxiliaryWeightedSummand P n t‖ ≤ C * Real.exp (-t) := by
  let E : ℕ → ℝ := fun n => polynomialExpBound P * Real.exp (-(Real.pi/2) * (n : ℝ)^2)
  have hE : Summable E :=
    (gaussianEnvelope_summable (q := Real.pi/2) (by positivity)).mul_left _
  refine ⟨∑' n, E n, tsum_nonneg (fun n =>
    mul_nonneg (polynomialExpBound_nonneg P) (Real.exp_nonneg _)), ?_⟩
  intro t ht
  have hB (n : ℕ) : ‖auxiliaryWeightedSummand P n t‖ ≤ E n * Real.exp (-t) :=
    auxiliaryWeightedSummand_le_exponential P n ht
  have hN : Summable (fun n => ‖auxiliaryWeightedSummand P n t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hB (hE.mul_right _)
  calc
    _ ≤ ∑' n, ‖auxiliaryWeightedSummand P n t‖ := norm_tsum_le_tsum_norm hN
    _ ≤ ∑' n, E n * Real.exp (-t) := hN.tsum_le_tsum hB (hE.mul_right _)
    _ = _ := by rw [tsum_mul_right]

#print axioms auxiliaryWeightedSummand_summable
#print axioms iteratedDeriv_auxiliaryTheta
#print axioms auxiliaryWeightedSeries_decay

end Nuttall
