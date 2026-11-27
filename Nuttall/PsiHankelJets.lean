import Nuttall.PhiJetSeries

namespace Nuttall

/-- A positive order derivative of an integrated kernel is a derivative
of the preceding integration level. The formula also applies above level zero. -/
theorem iteratedDeriv_succ_psi_succ (m j : ℕ) (t : ℝ) :
    iteratedDeriv (j + 1) (psi (m + 1)) t =
      -iteratedDeriv j (psi m) t := by
  have h : deriv (psi (m + 1)) = fun t => -psi m t :=
    funext fun s => (psi_succ_hasDerivAt m s).deriv
  rw [iteratedDeriv_succ', h, iteratedDeriv_fun_neg]

/-- Every positive-order entry of the first integrated kernel's Hankel matrix
is a theta jet. Its zeroth entry remains the single tail integral. -/
theorem iteratedDeriv_succ_psi_one_eq_tsum (j : ℕ) (t : ℝ) :
    iteratedDeriv (j + 1) (psi 1) t =
      -(∑' n, auxiliaryWeightedSummand (phiJetPolynomial j) n t) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ_psi_succ]
  change -iteratedDeriv j W5.Phi t = _
  rw [iteratedDeriv_phi_eq_tsum]

#print axioms iteratedDeriv_succ_psi_one_eq_tsum

end Nuttall
