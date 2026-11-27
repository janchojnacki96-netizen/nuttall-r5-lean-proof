import Nuttall.AuxiliarySeries
import Nuttall.PsiDerivatives

namespace Nuttall

open scoped ContDiff

/-- The termwise differentiability of every auxiliary jet gives all orders
of continuous differentiability of the auxiliary theta series. -/
theorem contDiff_auxiliaryTheta : ContDiff ℝ ∞ auxiliaryTheta := by
  apply contDiff_iff_iteratedDeriv.2
  have hd (k : ℕ) : Differentiable ℝ (iteratedDeriv k auxiliaryTheta) := by
    rw [funext (iteratedDeriv_auxiliaryTheta k)]
    intro t
    exact ((auxiliarySignedJet_hasDerivAt k t).const_mul ((-1:ℝ)^k)).differentiableAt
  exact ⟨fun k _ => (hd k).continuous, fun k _ => hd k⟩

theorem contDiff_phi : ContDiff ℝ ∞ W5.Phi := by
  have hd := (contDiff_infty_iff_deriv.1 contDiff_auxiliaryTheta).2
  have he : W5.Phi = fun t => (-(deriv auxiliaryTheta t + auxiliaryTheta t))/2 := by
    funext t
    linarith only [twice_phi_eq_neg_deriv_add t]
  rw [he]
  exact ((hd.add contDiff_auxiliaryTheta).neg).div_const 2

/-- Every tail integration level is smooth, including the low levels used
by the finite certificates. -/
theorem contDiff_psi (m : ℕ) : ContDiff ℝ ∞ (psi m) := by
  induction m with
  | zero => exact contDiff_phi
  | succ m ih =>
    apply contDiff_infty_iff_deriv.2
    refine ⟨fun t => (psi_succ_hasDerivAt m t).differentiableAt, ?_⟩
    rw [funext (fun t => (psi_succ_hasDerivAt m t).deriv)]
    exact ih.neg

#print axioms contDiff_psi

end Nuttall
