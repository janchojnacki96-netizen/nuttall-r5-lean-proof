import Nuttall.PhiComplexDisk
import Nuttall.PhiJetSeries
import Mathlib.Analysis.Complex.RealDeriv

namespace Nuttall

open Polynomial
open scoped ContDiff

private theorem phiComplexSummand_ofReal (n : ℕ) (t : ℝ) :
    phiComplexSummand n (t : ℂ) = (W5.phiSummand n t : ℂ) := by
  rw [W5.phiSummand_factor]
  unfold phiComplexSummand phiComplexCoordinate
  push_cast
  rw [show (5:ℂ)*(t:ℂ) = (t:ℂ)+4*(t:ℂ) by ring, Complex.exp_add]
  ring

private theorem iteratedDeriv_re_on_real {f : ℂ → ℂ} (hf : ContDiff ℂ ∞ f) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun x : ℝ => (f (x:ℂ)).re) t =
      (iteratedDeriv k f (t : ℂ)).re := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, funext ih]
    have hd : Differentiable ℂ (iteratedDeriv k f) :=
      (contDiff_iff_iteratedDeriv.mp hf).2 k (by simp)
    have hc := ((hd (t:ℂ)).hasDerivAt).comp_ofReal
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc).deriv

private theorem phiSummand_eq_auxiliary_deriv (n : ℕ) :
    W5.phiSummand n = fun t => -(deriv (auxiliarySummand n) t + auxiliarySummand n t)/2 := by
  funext t
  rw [(auxiliarySummand_hasDerivAt n t).deriv]
  ring

/-- The existing real jet polynomial is the derivative of the individual real theta term. -/
theorem iteratedDeriv_phiSummand_eq_auxiliary (j n : ℕ) (t : ℝ) :
    iteratedDeriv j (W5.phiSummand n) t =
      auxiliaryWeightedSummand (phiJetPolynomial j) n t := by
  have hg : ContDiff ℝ ∞ (auxiliarySummand n) := by unfold auxiliarySummand; fun_prop
  have hf := (contDiff_infty_iff_deriv.1 hg).2
  rw [phiSummand_eq_auxiliary_deriv, iteratedDeriv_div_const, iteratedDeriv_fun_neg,
    iteratedDeriv_fun_add (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt,
    ← iteratedDeriv_succ', iteratedDeriv_auxiliarySummand, iteratedDeriv_auxiliarySummand]
  simp only [auxiliaryWeightedSummand, phiJetPolynomial, eval_mul, eval_C, eval_sub, pow_succ]
  ring

/-- Cauchy's bound also controls the real jet terms in the actual theta series. -/
theorem phiJetSummand_norm_le (n k : ℕ) {c : ℝ} (hc : c ≤ 2) :
    ‖auxiliaryWeightedSummand (phiJetPolynomial k) n c‖ ≤
      (k.factorial : ℝ) * (20000 * Real.exp (-((n:ℝ)^2 * Real.pi * Real.exp (4*c))/3)) /
        (1/8 : ℝ)^k := by
  have hcd : ContDiff ℂ ∞ (phiComplexSummand n) := by
    unfold phiComplexSummand phiComplexCoordinate
    fun_prop
  have hreal : (fun x : ℝ => (phiComplexSummand n (x:ℂ)).re) = W5.phiSummand n :=
    funext (fun x => by rw [phiComplexSummand_ofReal, Complex.ofReal_re])
  rw [← iteratedDeriv_phiSummand_eq_auxiliary, ← hreal, iteratedDeriv_re_on_real hcd,
    Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (phiComplexSummand_iteratedDeriv_norm_le n k hc)

#print axioms phiJetSummand_norm_le

end Nuttall
