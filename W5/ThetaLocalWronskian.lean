import W5.ThetaInverseCoordinate

/-!
# Local theta-coordinate differentiation, avoiding the singular point x=0

The inverse function psiThetaCoordinate is relevant only on x>0.
Indeed its global extension through x=0 is not necessarily smooth.
This module replaces an unrealistically strong global-differentiability
hypothesis by pointwise differentiability ONLY on x>0.

The derivative identities and the Wronskian equality are exact,
while the required order-eight local smoothness of the original
theta series remains to be proved separately.
-/

namespace W5

theorem xOfT_pos_all (t : ℝ) : 0 < xOfT t := by
  unfold xOfT
  exact one_div_pos.mpr
    (Real.sqrt_pos.mpr (mul_pos Real.pi_pos (Real.exp_pos _)))

/-- Chain rule using only the right-half-line differentiability needed
at x = xOfT(t). No differentiability is requested at x=0. -/
theorem deriv_comp_xOfT_on_pos
    (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x) :
    deriv (fun t : ℝ => f (xOfT t)) =
      fun t : ℝ => thetaDerivOp f (xOfT t) := by
  funext t
  have houter := (hf (xOfT t) (xOfT_pos_all t)).hasDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => f (xOfT s))
      (deriv f (xOfT t) * (-2 * xOfT t)) t := by
    simpa only [Function.comp_def] using
      (houter.comp t (xOfT_hasDerivAt t))
  simpa only [thetaDerivOp, mul_comm] using hcomp.deriv

/-- Iterated chain rule on the positive x half-line, to any finite order. -/
theorem iteratedDeriv_comp_xOfT_on_pos
    (f : ℝ → ℝ) :
    ∀ n : ℕ,
      (∀ k < n, ∀ x : ℝ, 0 < x →
        DifferentiableAt ℝ ((thetaDerivOp^[k]) f) x) →
      iteratedDeriv n (fun t : ℝ => f (xOfT t)) =
        fun t : ℝ => ((thetaDerivOp^[n]) f) (xOfT t) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro h
      have hprev :
          ∀ k < n, ∀ x : ℝ, 0 < x →
            DifferentiableAt ℝ ((thetaDerivOp^[k]) f) x := by
        intro k hk x hx
        exact h k (Nat.lt_succ_of_lt hk) x hx
      have hnow :
          ∀ x : ℝ, 0 < x →
            DifferentiableAt ℝ ((thetaDerivOp^[n]) f) x :=
        h n (Nat.lt_succ_self n)
      rw [iteratedDeriv_succ, ih hprev]
      rw [deriv_comp_xOfT_on_pos ((thetaDerivOp^[n]) f) hnow]
      funext t
      rw [Function.iterate_succ_apply']

/-- Exact ORIGINAL order-five Wronskian in the explicit inverse
theta coordinate. Only differentiability on x>0 is assumed. -/
theorem W_five_eq_thetaWronskian_explicit_on_pos
    (hf : ∀ k < 9, ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ ((thetaDerivOp^[k]) psiThetaCoordinate) x)
    (t : ℝ) :
    W 5 t = thetaWronskian 5 psiThetaCoordinate (xOfT t) := by
  unfold W thetaWronskian
  congr 1
  apply Matrix.ext
  intro i j
  have hfun : Psi1 = fun s : ℝ => psiThetaCoordinate (xOfT s) := by
    funext s
    exact (psiThetaCoordinate_comp_xOfT s).symm
  have hsmall :
      ∀ k < i.val+j.val, ∀ x : ℝ, 0 < x →
        DifferentiableAt ℝ ((thetaDerivOp^[k]) psiThetaCoordinate) x := by
    intro k hk x hx
    exact hf k (by omega) x hx
  simpa only [hfun, Matrix.of_apply] using
    (congrFun
      (iteratedDeriv_comp_xOfT_on_pos psiThetaCoordinate
        (i.val+j.val) hsmall) t)

end W5
