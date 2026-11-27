import Nuttall.ThetaAuxiliary
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace Nuttall

open Polynomial

/-- Argument of the Gaussian factor in the auxiliary theta summand. -/
noncomputable def auxiliaryCoordinate (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ)^2 * Real.pi * Real.exp (4*t)

/-- Polynomial left over after factoring the auxiliary summand from its
signed derivative of order `j`. -/
noncomputable def auxiliaryDerivativePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | j+1 => (C 4 * X - C 5) * auxiliaryDerivativePolynomial j -
      C 4 * X * derivative (auxiliaryDerivativePolynomial j)

private theorem auxiliaryCoordinate_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (auxiliaryCoordinate n) (4 * auxiliaryCoordinate n t) t := by
  have hlin : HasDerivAt (fun x : ℝ => 4*x) 4 t := by
    simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
  have h := ((Real.hasDerivAt_exp (4*t)).comp t hlin).const_mul ((n : ℝ)^2 * Real.pi)
  convert h using 1 <;> simp only [auxiliaryCoordinate, Function.comp_apply] <;> ring

private theorem auxiliarySummand_hasDerivAt_factor (n : ℕ) (t : ℝ) :
    HasDerivAt (auxiliarySummand n)
      ((5 - 4 * auxiliaryCoordinate n t) * auxiliarySummand n t) t := by
  convert auxiliarySummand_hasDerivAt n t using 1
  simp only [auxiliaryCoordinate, auxiliarySummand, W5.phiSummand]
  rw [show (9 : ℝ)*t = 5*t + 4*t by ring, Real.exp_add]
  ring

/-- The recurrence holds at every theta index and every real argument. -/
theorem auxiliary_polynomial_summand_hasDerivAt (j n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => auxiliarySummand n s *
      (auxiliaryDerivativePolynomial j).eval (auxiliaryCoordinate n s))
      (-(auxiliarySummand n t *
        (auxiliaryDerivativePolynomial (j+1)).eval (auxiliaryCoordinate n t))) t := by
  have hpol := ((auxiliaryDerivativePolynomial j).hasDerivAt (auxiliaryCoordinate n t)).comp t
    (auxiliaryCoordinate_hasDerivAt n t)
  convert (auxiliarySummand_hasDerivAt_factor n t).mul hpol using 1
  · rfl
  · simp only [auxiliaryDerivativePolynomial, eval_sub, eval_mul, eval_C, eval_X]
    ring

/-- Formula for each signed derivative, before exchanging derivatives and the series. -/
theorem iteratedDeriv_auxiliarySummand (j n : ℕ) (t : ℝ) :
    iteratedDeriv j (auxiliarySummand n) t =
      (-1 : ℝ)^j * (auxiliarySummand n t *
        (auxiliaryDerivativePolynomial j).eval (auxiliaryCoordinate n t)) := by
  induction j generalizing t with
  | zero => simp [auxiliaryDerivativePolynomial]
  | succ j ih =>
    have hfun : iteratedDeriv j (auxiliarySummand n) = fun s =>
        (-1 : ℝ)^j * (auxiliarySummand n s *
          (auxiliaryDerivativePolynomial j).eval (auxiliaryCoordinate n s)) := funext ih
    rw [iteratedDeriv_succ, hfun,
      ((auxiliary_polynomial_summand_hasDerivAt j n t).const_mul ((-1 : ℝ)^j)).deriv,
      pow_succ]
    ring

#print axioms iteratedDeriv_auxiliarySummand

end Nuttall
