import Nuttall.PsiSmoothness

namespace Nuttall

open Polynomial
open scoped ContDiff

/-- The existing auxiliary theta series gives every derivative of the original kernel. -/
theorem iteratedDeriv_phi_eq_auxiliary (j : ℕ) (t : ℝ) :
    iteratedDeriv j W5.Phi t =
      -(iteratedDeriv (j + 1) auxiliaryTheta t + iteratedDeriv j auxiliaryTheta t) / 2 := by
  have he : W5.Phi = fun s => (-(deriv auxiliaryTheta s + auxiliaryTheta s)) / 2 := by
    funext s
    linarith only [twice_phi_eq_neg_deriv_add s]
  have hd := (contDiff_infty_iff_deriv.1 contDiff_auxiliaryTheta).2
  have hf : ContDiffAt ℝ j (deriv auxiliaryTheta) t := (hd.of_le (by simp)).contDiffAt
  have hg : ContDiffAt ℝ j auxiliaryTheta t :=
    (contDiff_auxiliaryTheta.of_le (by simp)).contDiffAt
  rw [he, iteratedDeriv_div_const, iteratedDeriv_fun_neg, iteratedDeriv_fun_add hf hg,
    ← iteratedDeriv_succ']

/-- The polynomial after factoring out the auxiliary summand from a kernel jet. -/
noncomputable def phiJetPolynomial (j : ℕ) : ℝ[X] :=
  C ((-1 : ℝ)^j / 2) * (auxiliaryDerivativePolynomial (j + 1) - auxiliaryDerivativePolynomial j)

theorem iteratedDeriv_phi_eq_tsum (j : ℕ) (t : ℝ) :
    iteratedDeriv j W5.Phi t = ∑' n, auxiliaryWeightedSummand (phiJetPolynomial j) n t := by
  have hs (k : ℕ) :=
    auxiliaryWeightedSummand_summable (auxiliaryDerivativePolynomial k) t
  rw [iteratedDeriv_phi_eq_auxiliary, iteratedDeriv_auxiliaryTheta, iteratedDeriv_auxiliaryTheta]
  have he (n : ℕ) : auxiliaryWeightedSummand (phiJetPolynomial j) n t =
      ((-1 : ℝ)^j / 2) * (auxiliaryWeightedSummand (auxiliaryDerivativePolynomial (j + 1)) n t -
        auxiliaryWeightedSummand (auxiliaryDerivativePolynomial j) n t) := by
    simp only [auxiliaryWeightedSummand, phiJetPolynomial, eval_mul, eval_sub, eval_C]
    ring
  simp_rw [he]
  rw [tsum_mul_left, (hs (j + 1)).tsum_sub (hs j), pow_succ]
  ring

/-- At the origin the Gaussian factor is an integer power of a single real constant. -/
theorem auxiliaryWeightedSummand_origin (P : ℝ[X]) (n : ℕ) :
    auxiliaryWeightedSummand P n 0 =
      ((n : ℝ)^2 * Real.pi) * P.eval ((n : ℝ)^2 * Real.pi) *
        Real.exp (-Real.pi)^(n^2) := by
  simp only [auxiliaryWeightedSummand, auxiliarySummand, auxiliaryCoordinate, mul_zero,
    Real.exp_zero, mul_one]
  rw [← Real.exp_nat_mul, Nat.cast_pow]
  rw [show (n : ℝ)^2 * -Real.pi = -(n : ℝ)^2 * Real.pi by ring]
  ring

#print axioms iteratedDeriv_phi_eq_tsum
#print axioms auxiliaryWeightedSummand_origin

end Nuttall
