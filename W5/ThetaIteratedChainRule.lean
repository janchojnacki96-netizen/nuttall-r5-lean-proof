import W5.ThetaDerivativeBridge

/-!
# Higher derivatives under the x(t) theta coordinate

Define D f(x) = -2*x*f'(x). The finite-order chain rule gives
(d/dt)^n f(x(t)) = (D^[n] f)(x(t)) whenever the required
intermediate functions are differentiable.

The order-5 Wronskians use derivatives up to n=8, and we state
a specialized lemma with only these finitely many smoothness
premises. It is a structural change-of-coordinate lemma, NOT an
assumption-free differentiability theorem for Psi1 or its infinite
theta expansion.
-/

namespace W5

/-- The exact differential operator transported by x(t) = 1/sqrt(pi*exp(4*t)). -/
noncomputable def thetaDerivOp (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (-2*x) * deriv f x

/-- First-order chain rule in the theta coordinate. -/
theorem deriv_comp_xOfT (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    deriv (fun t : ℝ => f (xOfT t)) =
      fun t : ℝ => thetaDerivOp f (xOfT t) := by
  funext t
  have hcomp : HasDerivAt (fun s : ℝ => f (xOfT s))
      (deriv f (xOfT t) * (-2 * xOfT t)) t := by
    simpa only [Function.comp_def] using
      ((hf (xOfT t)).hasDerivAt.comp t (xOfT_hasDerivAt t))
  simpa only [thetaDerivOp, mul_comm] using hcomp.deriv

/-- General finite-order iterated chain rule. The differentiability
assumptions cover precisely the intermediate orders k<n. -/
theorem iteratedDeriv_comp_xOfT (f : ℝ → ℝ) :
    ∀ n : ℕ,
      (∀ k < n, Differentiable ℝ ((thetaDerivOp^[k]) f)) →
      iteratedDeriv n (fun t : ℝ => f (xOfT t)) =
        fun t : ℝ => ((thetaDerivOp^[n]) f) (xOfT t) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro h
      have hprev : ∀ k < n, Differentiable ℝ ((thetaDerivOp^[k]) f) := by
        intro k hk
        exact h k (Nat.lt_succ_of_lt hk)
      have hnow : Differentiable ℝ ((thetaDerivOp^[n]) f) :=
        h n (Nat.lt_succ_self n)
      rw [iteratedDeriv_succ, ih hprev]
      rw [deriv_comp_xOfT ((thetaDerivOp^[n]) f) hnow]
      funext t
      rw [Function.iterate_succ_apply']

/-- The exact derivative orders that occur in a 5-by-5 Wronskian
matrix are all covered by the first nine operator iterates. -/
theorem wronskian_five_entry_comp_xOfT
    (f : ℝ → ℝ)
    (hf : ∀ k < 9, Differentiable ℝ ((thetaDerivOp^[k]) f))
    (i j : Fin 5) (t : ℝ) :
    iteratedDeriv (i.val + j.val)
        (fun s : ℝ => f (xOfT s)) t =
      ((thetaDerivOp^[i.val + j.val]) f) (xOfT t) := by
  have hsmall :
      ∀ k < i.val + j.val, Differentiable ℝ ((thetaDerivOp^[k]) f) := by
    intro k hk
    exact hf k (by omega)
  exact congrFun (iteratedDeriv_comp_xOfT f (i.val + j.val) hsmall) t

end W5
